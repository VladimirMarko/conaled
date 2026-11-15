module HaskellClient where

import Data.Either (Either(..), either)

-- Import and specialize the real base declaration; do not redefine either.
choose :: Bool -> Either Bool Bool -> Bool
choose mask = either (\x -> x /= mask) not

step :: Bool -> Either Bool Bool -> (Bool, Bool)
step state input = (state, choose state input)

run :: Bool -> [Either Bool Bool] -> [Bool]
run state [] = [state]
run state (input : rest) = let (out, next) = step state input
                         in out : run next rest

inputs :: [Either Bool Bool]
inputs = [Left False, Left True, Right False, Right True]

observations :: [Bool]
observations = [choose mask x | mask <- [False, True], x <- inputs]
            ++ run False inputs ++ run True inputs

-- Definedness discriminators outside the proposed total-input fragment.
unusedBottom :: Bool
unusedBottom = either (const True) (\_ -> undefined) (Left False)

forcedBottom :: Bool
forcedBottom = either id not (undefined :: Either Bool Bool)

unknownCallback :: (Bool -> Bool) -> Bool -> Bool
unknownCallback f x = f x
