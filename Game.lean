import Game.Levels.PrimeImpliesIrreducible

-- Here's what we'll put on the title screen
Title "Heidelberg Lean Game"
Introduction
"
Welcome to the Heidelberg Lean Game!

In this game, we explore a single world with 6 levels.
The final level (Level 6) proves that every natural number which is prime is irreducible.

More worlds will follow, so stay tuned!
"

Info "
A prototype for this game was created as part of the HEGL (Heidelberg Experimental Geometry Lab) Illustrating Mathematics Seminar 2024/2025 at the University of Heidelberg. For more details, visit the [Seminar page](https://matematiflo.github.io/HEGL_IMS_WiSe_2024/).

Credits:

- Heide Frank
- Johannes Kadel
- Levi Klein
- Adriano Messina
- Hanna Rothe
- Alina Stock
- Jonas Schäfer
- Vincent Voß
- Katrin Weiß

The current version is being developed and maintained by:

- Jonas Heese
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
