��    	      d      �       �   �  �     �  +  �	     �     �  >        ]     p  �       N  �  i  D  f     �  #   �  C   �     %     9               	                               # The Fibonacci Game, version 1.0.0.

## What is this game?

Welcome to The Fibonacci Game! In this game, you will get introduced
to the **LEAN** theorem prover, which will allow you to formalize
some results on Fibonacci numbers. Actually you will only prove one result,
but hopefully it will be lots of fun!

To get started, click on the first world, the blue circle labelled "Tutorial World", on the right.
Once you complete all the levels of the Tutorial World, hit "Main Menu" in the top left corner of the screen to get back here.
In this way, you will see that the first blue circle has turned into green, which
will give you access to the following world.
You can use this menu to navigate as you try more of the problems.

Have fun!

## Thanks

Some of this is based on materials from the BIYSC project on "Can computers do math?" at Universitat Autònoma de Barcelona.

Some of the explanations are taken/adapted from the original <a href="https://www.ma.imperial.ac.uk/~buzzard/xena/natural_number_game/"
  target="blank">Natural Number Game</a>.

Lean is a computer theorem prover being developed at Microsoft Research.

## Tactic cheat table

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

 ## The `assumption` tactic

The first tactic that we'll learn is the `assumption` tactic. This can be used
when your goal is exactly one of your hypotheses. In the following example,
there are three hypotheses, namely the fact that $a$ is $3$ (hypothesis `ha`), the
fact that $b$ is $4$ (hypothesis `hb`) and the fact that $c$ is $5$ (hypothesis `hc`).

Since we want to prove that $b=4$, which is one of our hypotheses, we should be able to
win by typing `assumption,` (**don't forget the comma**). Delete the `sorry` and try it.
 ## The `rw` tactic

The next tactic to learn is the `rw` tactic (short for `rewrite`). If we have a proof $h$ of an equality
$a=b$, then `rw h` will replace all occurrences of $a$ in the goal with $b$. It also works with `↔` instead of `=`.
That is, if we have two equivalent statements, it will replace one with the other.

In the example at hand, we have a proof $h$ of the fact that $a=3$. We want to prove that $a+5=8$,
which we could do by substituting in the value of $a$. Try to erase the `sorry` and replace it with
`rw h,` and see if it works.
 Fibonacci World If $a = 3$, then $a + 5 = 8$.
 If $a$ is $3$ and $b$ is $4$ and $c$ is $5$, then $b$ is $4$.
 The Fibonacci Game Tutorial World Project-Id-Version: 1.0.0
PO-Revision-Date: 
Last-Translator: 
Language-Team: 
Language: ca
MIME-Version: 1.0
Content-Type: text/plain; charset=utf-8
Content-Transfer-Encoding: 8bit
X-Generator: Poedit 3.2
 # El Joc de Fibonacci, versió 1.0.0.

## Què és aquest joc?

Benvinguts al Joc de Fibonacci! En aquest joc, se t'introduirà
al demostrador de teoremes **LEAN**, que et permetrà formalitzar
alguns resultats sobre els nombres de Fibonacci. De fet, només demostraràs un resultat,
però esperem que pel camí t'ho passis molt bé!

Per començar, clica sobre el primer "Món", el cercle blau que es diu "Tutorial", a la dreta.
Quan completis tots els nivells del Tutorial, clica a "Menú prnicipal" a dalt a l'esquerra de la pantalla per tornar a aquesta pantalla.
Aleshores veuràs que el primer cercle blau s'ha tornat verd, cosa que et donarà
accés al següent Món.
Pots fer servir aquest menú per navegar i provar més problemes.

Passa-t'ho bé!

## Agraïments

Parts d'aquest joc s'han basat en materials del projecte BIYSC en "Can computers do math?" a la Universitat Autònoma de Barcelona

Algunes explicacions estan agafades/adaptades de l'original <a href="https://www.ma.imperial.ac.uk/~buzzard/xena/natural_number_game/"
  target="blank">Natural Number Game</a>.

El Lean és un assistent de demostracions que està essent desenvolupat a Microsoft Research.

## Taula recordatori de tàctiques

Aquí sota pots trobar una referència ràpida per decidir quina tàctica et pot ser útil
en diferents contextes

| Si veus   | A l'objectiu          | A la hipòtesi `h`|
|=========|======================|==============================|
|∧        |   `split`          |        `cases h with h1 h2`  |
| ∨       |   `left` / `right`         |     `cases h`|
|→       |   `intro`          |        `have h' := h x`  |
| ↔       |   `split`         |     `cases h with h1 h2`|
|∀       |   `intro`         |        `have h' := h x`  |
| ∃       |   `use`         |     `cases h with x hx`|

 ## La tàctica `assumption`

La primera tàctica que aprendrem es diu `assumption`. Es pot fer servir
quan l'objectiu és exactament una de les teves hipòtesis. En l'exemple següent,
hi ha tres hipòtesis: el fet que $a$ és $3$ (hipòtesi `ha`), el
fet que $b$ és $4$ (hipòtesi `hb`) i el fet que $c$ és $5$ (hipòtesi `hc`).

Com que volem demostrar que $b=4$, que és una de les nostres hipòtesis, hauriem de
guanyar escrivint `assumption,` (**no t'oblidis la coma**). Esborra el `sorry`i prova-ho.
 ## La tàctica `rw`

La següent tàctica que aprendrem es diu `rw` (abreviatura de `rewrite`). Si tenim una demostració $h$ d'una igualtat
$a=b$, aleshores `rw h` substituirà cada vegada que trobi $a$ a l'objectiu amb una $b$. També funciona amb `↔` en comptes de `=`.
És a dir, si tenim dos enunciats equivalents, canviarà el primer pel segon.

En l'exemple que ens ocupa, tenim una demostració $h$ del fet que $a=3$. Volem demostrar que $a+5=8$,
cosa que podríem fer substituïnt el valor de $a$. Intenta esborrar el `sorry` i canvia'l per
`rw h,` i mira si funciona.
 El Món Fibonacci Si $a = 3$, aleshores $a + 5 = 8$.
 Si $a$ és $3$ i $b$ és $4$ i $c$ és $5$, aleshores $b$ és $4$.
 El Joc de Fibonacci Tutorial 