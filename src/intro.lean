/-
# The Fundamental Game, version 1.0.0.

## What is this game?

Welcome to The Fundamental Game! In this game, you will get introduced
to the **LEAN** theorem prover, which will allow you to formalize
some results that we have seen in class. Hopefully it will be lots of fun!

To get started, click on the first world, the blue circle labelled "Tutorial World", on the right.
Once you complete all the levels of the Tutorial World, hit "Main Menu" in the top left corner of the screen to get back here.
In this way, you will see that the first blue circle has turned into green, which
will give you access to the following world.
You can use this menu to navigate as you try more of the problems.

Have fun!

## Thanks

This game uses Mohammad Pedramfar's <a href="https://github.com/mpedramfar/Lean-game-maker">*Lean Game Maker* engine</a>.

Some of the explanations are taken/adapted from the original <a href="https://www.ma.imperial.ac.uk/~buzzard/xena/natural_number_game/"
  target="blank">Natural Number Game</a>, by Kevin Buzzard and Mohammad Pedramfar.

Lean is a computer theorem prover being developed at Microsoft Research.

## Tactic table

In this game you will learn the following tactics: `assumption`, `rw`, `intro`, `apply`,
`use`, `split`, `left`, `right`, `have`, `cases` and the more high-level `ring` and `group`.

Below you can find a quick reference to figure out which tactic may be useful
in different contexts

| If you see   | In goal          | In hypothesis `h`|
|=========|======================|==============================|
|∧        |   `split`          |        `cases h with h1 h2`  |
| ∨       |   `left` / `right`         |     `cases h`|
|→       |   `intro`          |        `have h' := h x`  |
| ↔       |   `split`         |     `cases h with h1 h2`|
|∀       |   `intro`         |        `have h' := h x`  |
| ∃       |   `use`         |     `cases h with x hx`|
| ¬       | `intro hc` |  ? |

-/

