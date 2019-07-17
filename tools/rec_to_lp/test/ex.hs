data Xbool = Xfalse | Xtrue
    deriving (Show, Eq, Ord)
    
notBool :: Xbool -> Xbool
andBool :: Xbool -> Xbool -> Xbool
xorBool :: Xbool -> Xbool -> Xbool

notBool Xfalse = Xtrue
andBool Xfalse l = Xfalse
xorBool Xtrue l = (notBool l)

main = do
 print (andBool Xtrue Xtrue)
 print (andBool (xorBool Xfalse Xtrue) Xtrue)