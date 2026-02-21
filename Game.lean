import Game.Levels.PrimeImpliesIrreducible
import Game.Levels.DemoWorld
import Game.Levels.StrIneqWorld

-- Here's what we'll put on the title screen
Title "Heidelberg Lean Game"
Introduction
"
Welcome to the Heidelberg Lean Game!

In this game, we explore a single world with 6 levels.
The final level (Level 6) proves that every natural number which is prime is irreducible.

The second world treats the equality relation `=` on the natural numbers ℕ. The final theorem of the world will be to establish that the equality relation on the naturals is decidable, constructively.
(Note: This means, that in vanilla lean, all the theorems do not require any of the axioms `[propext]`, `[Classical.choice]`, `[Quot.sound]`, that is, propositional extensionality, choice, and the soundness of the quotient construction.)

The third world covers elemenetary properties of strict orderings and strict inequalities. In the first half we will prove positive results, and continue to show that these results are sharp in the second half of the world, by constructing a common counterexample.
"

Info "
A prototype for this game was created as part of the HEGL (Heidelberg Experimental Geometry Lab) Illustrating Mathematics Seminar 2024/2025 at the University of Heidelberg. For more details, visit the [Seminar page](https://matematiflo.github.io/HEGL_IMS_WiSe_2024/).

Credits:

- Heide Frank
- Johannes Kadel
- Adriano Messina
- Hanna Rothe
- Alina Stock
- Jonas Schäfer
- Vincent Voß
- Katrin Weiß

The current version is being developed and maintained by:

- Heide Frank
- Levi Klein
- Kevin Klinge
- Florent Schaffhauser
"

/-! Information to be displayed on the servers landing page. -/
Languages "en"
CaptionShort "Game Template"
CaptionLong "You should use this game as a template for your own game and add your own levels."
-- Prerequisites "" -- add this if your game depends on other games
-- CoverImage "images/cover.png"

/-! Build the game. Show's warnings if it found a problem with your game. -/
MakeGame
