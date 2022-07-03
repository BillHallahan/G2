module G2.Equiv.Config where

-- Config options
data NebulaConfig = NC { use_labeled_errors :: UseLabeledErrors
                          , sync :: Bool }

data UseLabeledErrors = UseLabeledErrors | NoLabeledErrors deriving (Eq, Show, Read)
