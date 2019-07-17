notBool :: Xbool -> Xbool
andBool :: Xbool -> Xbool -> Xbool
BuildOctet :: Xbool

X0 :: Xbool
X1 :: Xbool

x00 = (BuildOctet X0 X0 X0 X0 X0 X0 X0 X0)
x01 = (BuildOctet X0 X0 X0 X0 X0 X0 X0 X1)

andBool X0 b = b

main = do
 print (BuildOctet X0 X1)