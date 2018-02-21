module G2.Internals.Liquid.SpecialAsserts (addSpecialAsserts) where

import G2.Internals.Language
import qualified G2.Internals.Language.ExprEnv as E
import qualified G2.Internals.Language.KnownValues as KV

addSpecialAsserts :: State t -> State t
addSpecialAsserts s@(State { expr_env = eenv
						   , type_env = tenv
						   , known_values = kv}) =
	let
		pe = KV.patErrorFunc kv
		e = case E.lookup pe eenv of
			Just e2 -> e2
			Nothing -> Prim Undefined TyBottom

		fc = FuncCall {funcName = pe, arguments = [], returns = Prim Undefined TyBottom}
		false = mkFalse kv tenv
		e' = Assert (Just fc) false e
	in
	s {expr_env = E.insert pe e' eenv}