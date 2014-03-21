MACHINE FunctionsAsRelationsTest
PROPERTIES

/* The following functions are translated as relations */

/* total function */
{{(1,3),(1+1,3)}} = {1,2} --> {3}
& {(1+1,1)} : {2} --> NATURAL

/* total injectiv function */
& {{(1,3), (2,4)}, {(1,4),(2,3)}} = {1,2} >-> {3,4}
& {(1,1)} : {1} >-> NATURAL

/* total surjectiv function */
& {{(1,3), (2,4)}, {(1,4),(2,3)}} = {1,2} -->> {3,4}
& {(1,1)} : {1} -->> {1}

/* total bijectiv function */
& {} = {1,2,3} >-> {3,4}
& {(1,1)} : {1} >-> {1}


/* partial function */
& {{}, {(1,1)}, {(2,1)}, {(1,1), (2,1)}} = {1,2} +-> {1} 
& {(1,1)} : NATURAL +-> NATURAL

/* partial surjectiv function */
& {{(1,1)}, {(2,1)}, {(1,1), (2,1)}} = {1,2} +->> {1} 
& {(1,1)} : NATURAL +-> {1}

/* partial injectiv function */
& {{}, {(1,1)}, {(2,1)}}= {1,2} >+> {1} 
& {(1,1)} : NATURAL >+> {1}

/* partial bijectiv function */
& {{(1,1)}, {(2,1)}}= {1,2} >+>> {1} 
& {(1,1)} : NATURAL >+>> {1}

END
