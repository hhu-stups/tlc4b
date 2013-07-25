MACHINE BBuiltInsTest
PROPERTIES
/* strict subset */
{1} <<: {1,2}
& {} <<: {1}
& not({} <<: {})
& not({1} <<: {1})

/* not subset */
& {1} /<: {2}
& {1,2} /<: {2}
& not({1} /<: {1,2})
& not({1} /<: {1})

/* not strict subset */
& {1} /<<: {2}
& {1} /<<: {1}
& {} /<<: {}
& not({1} /<<: {1,2})
& not({} /<<: {1})

/* POW1 */
& POW1({}) = {}
& POW1({1}) = {{1}}
& POW1({1,2}) = {{1}, {2}, {1,2}}

/* FIN */
& FIN({}) = {{}}
& FIN({1}) = {{}, {1}}
& FIN({1,2}) = {{}, {1}, {2}, {1,2}}

/* FIN1 */
& FIN1({}) = {}
& FIN1({1}) = {{1}}
& FIN1({1,2}) = {{1}, {2}, {1,2}}

/* Quantified intersection */
& INTER(z).(z: {1,2}| {z}) = {}
& INTER(x1).(x1: {2,4}| {y1 | y1 : 0..10 & y1 <= x1}) = {0,1,2}

/* Quantified union */
& UNION(z).(z: {1,2}| {z}) = {1,2}
& UNION(x1).(x1: {2,4}| {y1 | y1 : 0..10 & y1 <= x1}) = {0,1,2,3,4}

/* Sigma */
& SIGMA(z).(z : {1,2,3}| z+z) = 12
& SIGMA(z).(z : {1,2,3} & 1=1| z+z) = 12
& SIGMA(x).(x : {1,2,3}| x+1) = 9

/* Pi */
& PI(z).(z : {1,2,3}| z+z) = 12
& PI(z).(z : {1,2,3} & 1=1| z+z) = 12
& PI(x).(x : {1,2,3}| x) = 6

/* Successor */
& succ(3) = 4
& succ(0) = 1
& succ(-1) = 0

/* Predecessor */
& pred(3) = 2
& pred(1) = 0
& pred(0) = -1

/* Minimum */
& min({1}) = 1
& min({1,2}) = 1

/* Maximum */
& max({1}) = 1
& max({1,2}) = 2

/* MaxInt */
& MAXINT = 4

/* MinInt */
& MININT = -1

END