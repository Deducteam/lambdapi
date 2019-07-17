BEGIN {
    special["="] = 1
    special["main"] = 1
    special["do"] = 1
    special["data"] = 1
    special["|"] = 1
}

## Symbol declaration
/::/ {
    sub(/::/, ":") ;
    r = gensub(/^([^:]+) : (.*)$/,
               "symbol \\1 : \\2", "1") ;
    context[$1] = 1 ;
    q = gensub(/->/, "⇒", "g", r) ;
    print q
}
/print/ { sub(/\s*print/, "compute") ; print }

## Take a dirty identifier (i.e. possibly with a surrounding
## parenthesis), cleans it and determine whether it is a variable
function is_var(ident) {
    # Remove parens around field
    clean = gensub(/\(?(\w+)\)?/, "\\1", "1", $i) ;
    # If the first letter is uppercase, identifier is a constructor
    # defined by a 'data'
    first_up = match(clean, /[A-Z]/) ;
    is_constructor = first_up == 1 ;
    is_special = clean in special ;
    is_defined = clean in context ;
    return !is_constructor && !is_special && !is_defined
}
## Rewrite rules
## Do not process 'main = do' line
($1 !~ /main|data/) && /=/ {
    for (i = 1; i <= NF; i++) {
        if (is_var($i))
            $i = "\&"$i
    }
    t = gensub(/^([^=]+) = (.*)$/,
               "rule \\1 → \\2", "1") ;
    print t
}
## Variant
## Pattern describe "data with at least one bar"
/data [^\|]*\|/ {
    type_ident = gensub(/^data ([A-Z]\w*) = .*/, "\\1", "1") ;
    printf("symbol %s : TYPE\n", type_ident)
    rhs = gensub(/[^=]*= (.*)$/, "\\1", "1") ;
    split(rhs, sep_constr, "|") ;
    for (c in sep_constr) {
        printf("symbol %s : %s\n", sep_constr[c], type_ident)
    }
}
## Records
## Pattern: data with no bars
/data [^\|]*$/ {
    type_ident = gensub(/^data ([A-Z]\w*) = .*/, "\\1", "1") ;
    printf("symbol %s : TYPE\n", type_ident) ;
    rhs = gensub(/[^=]*= (.*)$/, "\\1", "1") ;
    # Get record constructor
    rec_constr = gensub(/^(\S+).*/, "\\1", "1", rhs) ;
    fields = gensub(/^\S+\s(.*)$/, "\\1", "1", rhs) ;
    fields_arr = gensub(/\s/, " ⇒ ", "g", fields) ;
    printf("symbol %s : %s %s\n", rec_constr, fields_arr, type_ident)
}
END {}
