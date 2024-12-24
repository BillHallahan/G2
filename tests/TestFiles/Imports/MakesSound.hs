module MakesSound (makesSound, module Types) where

import Types

makesSound :: Animal -> Sound
makesSound Dog = Woof
makesSound Cat = Meow
makesSound Cow = Moo