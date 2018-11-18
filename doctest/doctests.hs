module Main (main) where

import           Test.DocTest

main :: IO ()
main =
    doctest
        [ "-isrc"
        , "src/"
        , "-XDeriveFoldable"
        , "-XDeriveFunctor"
        , "-XDeriveTraversable"
        , "-XTypeInType"
        , "-XDataKinds"
        , "-XTypeFamilies"
        , "-XTypeFamilyDependencies"
        , "-XBangPatterns"
        , "-XGADTs"
        , "-XLambdaCase"
        , "-XRankNTypes"
        , "-XTypeApplications"
        , "-XConstraintKinds"
        , "-XTypeOperators"
        , "-XScopedTypeVariables"
        , "-XConstraintKinds"
        , "-XStandaloneDeriving"
        , "-XBlockArguments"
        , "-XDeriveGeneric"
        , "-XDeriveLift"
        , "-XDerivingVia"
        , "-XEmptyCase"
        , "-XUnicodeSyntax"
        , "-XMultiParamTypeClasses"
        , "-XFunctionalDependencies"
        , "-XGeneralisedNewtypeDeriving"
        , "-XKindSignatures"
        , "-XQuantifiedConstraints"
        , "-XViewPatterns"
        , "-XPatternSynonyms"
        , "-XPolyKinds"
        , "-XNoStarIsType"
        ]
