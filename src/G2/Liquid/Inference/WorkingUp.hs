module G2.Liquid.Inference.WorkingUp ( WorkingUp
                                     , workingUp

                                     , allMembers
                                     , memberWU
                                     , insertWU
                                     , deleteWU ) where

import G2.Language

import qualified Data.HashSet as S

newtype WorkingUp = WorkingUp (S.HashSet Name) deriving (Show, Read)

workingUp :: WorkingUp
workingUp = WorkingUp S.empty

allMembers :: WorkingUp -> S.HashSet Name
allMembers (WorkingUp hs) = hs

memberWU :: Name -> WorkingUp -> Bool
memberWU n (WorkingUp wu) = S.member (zeroOutUnq n) wu

insertWU :: Name -> WorkingUp -> WorkingUp
insertWU n wd@(WorkingUp wu) =
    WorkingUp $ S.insert (zeroOutUnq n) wu

deleteWU :: Name -> WorkingUp -> WorkingUp
deleteWU n wd@(WorkingUp wu) =
    WorkingUp $ S.delete (zeroOutUnq n) wu

zeroOutUnq :: Name -> Name
zeroOutUnq (Name n m _ l) = Name n m 0 l
