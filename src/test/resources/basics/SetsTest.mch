MACHINE SetsTest
PROPERTIES
 union({{},{1},{1},{2},{2,3},{4}}) = {1,2,3,4}
& union({}) = {}
& UNION(x).(x :{2,4} | {y | y : 0..x}) = {0, 1, 2, 3, 4}
& (1,TRUE,2) : {a,b,c | a : {1} & b : {TRUE} & c : {2}}
& UNION(z).(z: {1,2} & 1 = 1| {z}) = {1,2}
END