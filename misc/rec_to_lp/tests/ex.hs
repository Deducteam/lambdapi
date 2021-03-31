data Nat = D0 | S Nat
    deriving (Show, Eq, Ord)

data Xbool = Xfalse | Xtrue
    deriving (Show, Eq, Ord)

data Bit = X0 | X1
  deriving (Show, Eq, Ord)

data Octet = BuildOctet Bit Bit Bit Bit Bit Bit Bit Bit
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
