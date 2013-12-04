MACHINE SequencesAsRelationsTest
CONSTANTS s, s2, s3, empty
PROPERTIES
s = {(1,1)}
& s2 = {(1,2)}
& s3 = {(1,1),(2,2), (3,3)}
& empty = {}
& s \/ {} = s /* force the typechecker to use sequences as relations */
& s2 \/ {} = s2  /* force the typechecker to use sequences as relations */
& s3 \/ {} = s3  /* force the typechecker to use sequences as relations */
& empty \/ {} = empty /* force the typechecker to use sequences as relations */

& empty = []
& s = [1]

/* Set of sequences */
& s : seq({1})
& s2 /: seq({1})
& not(s /: seq({1}))
& empty : seq({1})
& empty : seq({})


/* Set of sequences */
& s : seq1({1})
& empty /: seq1({})
& s2 /: seq1({1}) 
& not({} : seq1({1}))
& not({} : seq1({}))

/* Set of injective sequences */
& iseq({}) = {{}}
& iseq({1}) = {{},{(1,1)}}

/* Set of non empty injective sequences */
& iseq1({}) /= {{}}
& iseq1({1}) = {s}

/* Size */
& size(empty) = 0
& size(s3) = 3

/* Concatenation */
& s^{(1,2)} = {(1,1),(2,2)}
& s^{} = {(1,1)}
& {}^s3 = {(1,1),(2,2),(3,3)}
& {}^{} = empty

/* Prepand */
& 1 -> {(1,2),(2,3)} = s3
& 1 -> {} = s

/* Append */
& {(1,1),(2,2)} <- 3 = s3
& empty <- 1 = {(1,1)}

/* Front */
& front({(1,1)}) = empty
& front(s3) = {(1,1),(2,2)}

/* First */
& first(s) = 1
& first(s3) = 1

/* Tail */
& tail(s) = {}
& tail(s3) = {(1,2),(2,3)}

/* Last */
& last(s) = 1
& last(s3) = 3

/* Reverse */
& rev(empty) = {}
& rev(s) = {(1,1)}
& rev(s3) = {(1,3),(2,2),(3,1)}

/* Generalized Concatenation */
& conc({(1,{(1,1),(2,2)}),(2,{(1,3)})}) = s3
& conc({(1,s3),(2,{})}) = s3
& conc({(1,{}), (2,s3)}) = s3
& conc({(1,empty),(2,{})}) = {}

/* Perm */
& perm({3,4}) = {{(1,3)}\/ {(2,4)},{(1,4),(2,3)}}
& perm(empty) = {{}}

/* Take first elements */
& s3 /|\ 1 = {(1,1)}
& s3 /|\ 3 = s3
& s /|\ 0 = {}
& empty /|\ 0 = {}

& s3 \|/ 2 = {(1,3)}
& s3 \|/ 0 = s3
& s \|/ 1 = {}
& empty \|/ 0 = {}
END