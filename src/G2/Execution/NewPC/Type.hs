module G2.Execution.NewPC.Type( NewPC (..), newPCEmpty) where
import G2.Language (State)
import G2.Language.PathConds
import G2.Language.Syntax (Id)

data NewPC t = NewPC { state :: State t
                     , new_pcs :: [PathCond]
                     , concretized :: [Id] }


newPCEmpty :: State t -> NewPC t
newPCEmpty s = NewPC { state = s, new_pcs = [], concretized = []}
