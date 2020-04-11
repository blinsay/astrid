use std::collections::HashMap;
use std::f32::consts::FRAC_PI_2 as PI_2;
use std::io;
use std::ops::{AddAssign, Mul};

use clap::clap_app;
use rand::seq::SliceRandom;
use rand::Rng;
use svg::{node::element::path::Data as SVGData, node::element::Path as SVGPath};

fn main() {
    let arg_matches = clap_app!(astrid =>
        (about: "generate L-systems")
        (version: "0.69")
        (@arg delta: -d --delta +takes_value {valid_angle} "Size of the angle to turn at. Only used if an SVG is produced")
        (@arg svg: -s --svg "write an SVG to stdout")
        (@arg iterations: -n --iterations +takes_value {valid_usize} "The number of times to apply the rewrite rule")
        (@arg pattern: * +takes_value "The pattern to rewrite")
        (@arg rewrite_rules: +takes_value {valid_rule} * ... "A rewrite rule")
    )
    .get_matches();

    let input_pattern = arg_matches
        .value_of("pattern")
        .expect("pattern is required");
    let delta = arg_matches
        .value_of("delta")
        .unwrap_or("90")
        .parse::<f32>()
        .expect("should have validated degrees")
        .to_radians();

    let iterations: usize = arg_matches
        .value_of("iterations")
        .unwrap_or("1")
        .parse()
        .expect("invalid number of iterations");

    let rewrite_rules: RewriteRules = arg_matches
        .values_of("rewrite_rules")
        .expect("rewrite rules are required by arg parsing")
        .map(|s| parse_rule(s).expect("rule validation is required by arg parsing"))
        .collect();

    let mut string: Vec<char> = input_pattern.chars().collect();
    let mut strings = vec![string.clone()];
    for _ in 0..iterations {
        string = rewrite_rules.rewrite_string(string);
        strings.push(string.clone());
    }

    if arg_matches.is_present("svg") {
        // try to render an SVG. this only works if the L-system included the
        // turtle alphabet in its set of symbols.
        let doc = match paths_to_svg(turtle_walk(delta, 10.0, &string)) {
            Some(doc) => doc,
            None => {
                eprintln!("error: there's nothing to draw. Run astrid --help for more info.");
                return;
            }
        };

        let stdout = io::stdout();
        if let Err(e) = svg::write(stdout.lock(), &doc) {
            eprintln!("error writing svg output: {}", e);
        }
    } else {
        // show some nice text output. don't truncate any strings - the user
        // asked to see everything!
        let rule_string = rewrite_rules
            .iter()
            .map(|rule| format_rule(rule))
            .collect::<Vec<_>>()
            .join("\n            ");

        let generations = strings
            .iter()
            .skip(1)
            .map(|v| v.iter().collect::<String>())
            .collect::<Vec<_>>()
            .join("\n            ");

        println!("     rules: {}", rule_string);
        println!("iterations: {}", iterations);
        println!("     input: {}", input_pattern);
        println!("    output: {}", generations);
    }
}

fn valid_usize(v: String) -> Result<(), String> {
    v.parse::<usize>()
        .map(|_| ())
        .map_err(|_| String::from("must be a positive number"))
}

fn valid_angle(v: String) -> Result<(), String> {
    match v.parse::<f32>() {
        Ok(n) if 0.0 <= n && n <= 90.0 => Ok(()),
        _ => Err(String::from(
            "must be a valid angle between 0 and 90 degrees",
        )),
    }
}

fn valid_rule(v: String) -> Result<(), String> {
    parse_rule(&v).map(|_| ())
}

// A single rewrite rule mapping a character to a replacement sequence.
//
// For rewriting a->ab or F->FF-F-F-F-F-F+F.
type RewriteRule = (char, Vec<char>);

static INVALID_RULE_MSG: &'static str = "invalid rewrite rule: rules look like 'p=s'";

fn parse_rule(s: &str) -> Result<RewriteRule, String> {
    let parts: Vec<_> = s.splitn(2, "=").collect();

    let (pattern, replacement) = match &parts[..] {
        &[pattern, replacement] => (pattern, replacement),
        _ => return Err(String::from(INVALID_RULE_MSG)),
    };

    let pattern = pattern.trim().chars().next();
    let replacement: Vec<_> = replacement.trim().chars().collect();
    match (pattern, replacement) {
        (Some(pattern), replacement) if replacement.len() > 0 => Ok((pattern, replacement)),
        _ => Err(String::from(INVALID_RULE_MSG)),
    }
}

fn format_rule((p, s): RewriteRule) -> String {
    format!("{} -> {}", p, s.iter().collect::<String>())
}

#[cfg(test)]
mod test_rewrite_rule {
    use super::*;

    #[test]
    fn test_parse_rule() {
        assert_eq!(Ok(('f', vec!['f', '+', '-'])), parse_rule("f = f+-"));
        assert_eq!(Ok(('f', vec!['f', 'f'])), parse_rule("f=ff"));
        assert_eq!(Ok(('-', vec!['f'])), parse_rule("-=f"));
        assert_eq!(Ok(('-', vec!['='])), parse_rule("-=="));
        assert_eq!(Err(String::from(INVALID_RULE_MSG)), parse_rule("="));
        assert_eq!(Err(String::from(INVALID_RULE_MSG)), parse_rule(" = "));
        assert_eq!(Err(String::from(INVALID_RULE_MSG)), parse_rule("f="));
        assert_eq!(Err(String::from(INVALID_RULE_MSG)), parse_rule("=f"));
        assert_eq!(Err(String::from(INVALID_RULE_MSG)), parse_rule("f - "));
        assert_eq!(Err(String::from(INVALID_RULE_MSG)), parse_rule("f->ff"));
    }
}

// A set of rewrite rules (or production rules) for rewriting sequences. Should
// be applied all at once to an input string.
//
// Allows specifying multiple rewrite rules for the same input. If an input has
// multiple possible rules, one will be chosen at random. A set of rules with
// only one choice per input is a deterministic context-free L-system (or a
// DOL-System), and a set of rules with more than one choice for some input is
// a stochastic context-free L-system (just an OL-system).
#[derive(Debug)]
struct RewriteRules {
    rules: HashMap<char, Vec<Vec<char>>>,
}

impl RewriteRules {
    fn rewrite_char<R: Rng + ?Sized>(&self, c: char, r: &mut R) -> Option<&[char]> {
        self.rules
            .get(&c)
            .map(|cs| cs.choose(r).unwrap().as_slice())
    }

    fn rewrite_string<S>(&self, s: S) -> Vec<char>
    where
        S: IntoIterator<Item = char>,
    {
        let mut rng = rand::thread_rng();
        let rewrite_or_default = |c: char| {
            self.rewrite_char(c, &mut rng)
                .map(|s| s.to_vec())
                .unwrap_or(vec![c])
        };

        s.into_iter().flat_map(rewrite_or_default).collect()
    }

    fn iter<'a>(&'a self) -> impl Iterator<Item = (char, Vec<char>)> + 'a {
        self.rules
            .iter()
            .flat_map(|(&k, vs)| vs.iter().cloned().map(move |v| (k, v)))
    }
}

impl std::iter::FromIterator<RewriteRule> for RewriteRules {
    fn from_iter<I>(iter: I) -> Self
    where
        I: IntoIterator<Item = RewriteRule>,
    {
        let mut rules = HashMap::new();
        for (pred, succ) in iter.into_iter() {
            rules.entry(pred).or_insert_with(Vec::new).push(succ);
        }
        RewriteRules { rules }
    }
}

#[cfg(test)]
mod test_rewrite_rules {
    use super::*;

    #[test]
    fn test_rewrite_rules_from_iter() {
        // anabena catenula
        let rules = vec![('a', vec!['a', 'b']), ('b', vec!['a'])];
        let rules: RewriteRules = rules.into_iter().collect();
        assert_eq!(
            rules.rewrite_string("abab".chars()),
            "abaaba".chars().collect::<Vec<_>>()
        );
    }
}

// turtle interpretation of strings
//
// interprets an L-system string as a turlte walk. handles brancing and
// pen-up/pen-down instructions.
fn turtle_walk(delta: f32, step_size: f32, string: &[char]) -> Vec<Vec<Point>> {
    // most visual coordinate planes grow right and down, but plants drawn
    // by this turtle should look like they're growing up. start the turtle
    // facing "down" so it matches our intutition
    let mut heading = -PI_2;
    let mut position = Point::zero();
    let mut stack = vec![];
    let mut paths = vec![];
    let mut current_path = vec![position];

    for chr in string.iter() {
        match chr {
            // pen-up, move
            'f' => {
                paths.push(current_path);
                position += step_size * Point::unit_vec(heading);
                current_path = vec![position];
            }
            // pen-down, move
            'F' => {
                position += step_size * Point::unit_vec(heading);
                current_path.push(position);
            }
            // rotate left
            '+' => {
                heading += delta;
            }
            // rotate right
            '-' => {
                heading -= delta;
            }
            // push a turtle on to the stack
            '[' => {
                stack.push((heading, position, current_path));
                current_path = vec![position];
            }
            // pop a turtle off of the stack, saving the path made at the
            // previous level
            ']' => {
                if let Some((saved_heading, saved_position, saved_path)) = stack.pop() {
                    if current_path.len() > 1 {
                        paths.push(current_path);
                    }
                    // destructuring assignment isn't allowed :(
                    heading = saved_heading;
                    position = saved_position;
                    current_path = saved_path;
                }
            }
            _ => { /* do nothing */ }
        }
    }

    if current_path.len() > 1 {
        paths.push(current_path);
    }
    paths
}

#[derive(Debug, PartialEq, Clone, Copy)]
struct Point {
    x: f32,
    y: f32,
}

impl Point {
    fn zero() -> Point {
        Point { x: 0.0, y: 0.0 }
    }

    fn unit_vec(theta: f32) -> Point {
        Point {
            x: theta.cos(),
            y: theta.sin(),
        }
    }

    fn zip_map<F>(&self, other: &Point, f: F) -> Point
    where
        F: Fn(f32, f32) -> f32,
    {
        Point {
            x: f(self.x, other.x),
            y: f(self.y, other.y),
        }
    }
}

impl AddAssign for Point {
    fn add_assign(&mut self, other: Point) {
        self.x += other.x;
        self.y += other.y;
    }
}

impl Mul<Point> for f32 {
    type Output = Point;

    fn mul(self, other: Point) -> Point {
        Point {
            x: other.x * self,
            y: other.y * self,
        }
    }
}

// directly convert some paths to an SVG. any scaling or offsetting should
// get handled elsewhere.
fn paths_to_svg(paths: Vec<Vec<Point>>) -> Option<svg::Document> {
    let (min, max, width, height) = viewbox(paths.iter().flatten())?;
    let style_path = |pathdata: SVGData| {
        SVGPath::new()
            .set("fill", "none")
            .set("stroke", "black")
            .set("stroke-width", 3)
            .set("d", pathdata)
    };

    let doc = svg::Document::new().set("viewBox", format!("{} {} {} {}", min, max, width, height));
    let doc = paths
        .iter()
        .filter_map(pathdata)
        .map(style_path)
        .fold(doc, |doc, path| doc.add(path));

    Some(doc)
}

fn pathdata(path: &Vec<Point>) -> Option<SVGData> {
    let mut points = path.iter();
    let first = points.next()?;

    let data = SVGData::new().move_to((first.x, first.y));
    Some(points.fold(data, |data, point| data.line_to((point.x, point.y))))
}

// calculate the svg viewbox for a set of points
fn viewbox<'a, I>(mut points: I) -> Option<(f32, f32, f32, f32)>
where
    I: Iterator<Item = &'a Point>,
{
    // f32 only implements PartialOrd not Ord. these funcs pretend that
    // floats act like regular-ass numbers.
    #[rustfmt::skip]
    fn f32_min(a: f32, b: f32) -> f32 {
        if a < b { a } else { b }
    }
    #[rustfmt::skip]
    fn f32_max(a: f32, b: f32) -> f32 {
        if a > b { a } else { b }
    }

    let first = *points.next()?;
    let min = first;
    let max = first;

    let (min, max) = points.fold((min, max), |(min, max), point| {
        (point.zip_map(&min, f32_min), point.zip_map(&max, f32_max))
    });

    let width = max.x - min.x;
    let height = max.y - min.y;
    Some((min.x, min.y, width, height))
}
