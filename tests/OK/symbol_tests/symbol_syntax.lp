symbol U : TYPE
symbol tt : U
// symbol or opaque symbol or symbol or opaque symbol
symbol id ≔ λu:U,u
symbol id2 : U → U ≔ λu:U,u
symbol id3 : U → U ≔
begin
  assume u
  apply u
end
