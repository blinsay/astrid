# astrid

`astrid` is a CLI for playing with L-systems.

### Rewriting Strings

L-systems are string-rewriting systems that take a string and replace every
character according to some rule. `astrid` takes a string and some rewrite
rules as CLI arguments and will rewrite a string `-n` times.

```
$ astrid a 'a=ab' 'b=a' -n 7
     rules: b -> a
            a -> ab
     input: a
iterations: 7
    output: a
            ab
            aba
            abaab
            abaababa
            abaababaabaab
            abaababaabaababaababa
            abaababaabaababaababaabaababaabaab
```

> NOTE: It's a good idea to quote patterns and your rewrite rules so
> they don't get interpreted as shell special charachters.

### Turtle Graphics

`astrid` can interpret L-systems as [Turtle graphics programs](racket) and draw
an SVG. Any L-system that contains turtle control characters can be drawn

Running `astrid x 'x=F[+x]F[-x]+x' 'F=FF' -n 7 --svg -d 20` produces this
drawing.

<img src="example.svg" alt="l-system" height="400">

The turtle knows how to interpret the following commands:

Command | Description
--- | ---
`F` | Move forward, drawing a line.
`f` | Move forward, without drawing a line.
`+` | Turn left (counter-clockwise) by a fixed amount
`-` | Turn right (clockwise) by a fixed amount
`[` | Save the current turtle's position and direction on the stack. Doesn't move the turtle.
`]` | Return the turtle to the position and direction it had at the matching `[`. Doesn't draw a line.
