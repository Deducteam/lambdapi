/^require /{gsub("[.]","/");gsub(";","");gsub("[{][|]","");gsub("[|][}]","")}
/^require private open /{for(i=4;i<=NF;i++){if($i=="as"){i++}else{printf" %s.lpo",$i}};printf"\n";next}
/^require open /{for(i=3;i<=NF;i++){if($i=="as"){i++}else{printf" %s.lpo",$i}};printf"\n";next}
/^require /{for(i=2;i<=NF;i++){if($i=="as"){i++}else{printf" %s.lpo",$i}};printf"\n";next}
