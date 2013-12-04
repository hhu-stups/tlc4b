MACHINE SetsTest
PROPERTIES
 union({{},{1},{1},{2},{2,3},{4}}) = {1,2,3,4}
& union({}) = {}
& UNION(x).(x :{2,4} | {y | y : 0..x}) = {0, 1, 2, 3, 4}
END