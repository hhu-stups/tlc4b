MACHINE MultOrCart
PROPERTIES
/* mult */
2*3 = 6 
& 1 * 2 * 3 = 3 * 2
/* cart */
& {1}*{2} = {(1,2)}
& {1}*{2}*{3} = {(1,2,3)}
& {x,y,z | x : {1} & y : {2} & z : {1,3} & x = z} = {(1,2,1)}
END