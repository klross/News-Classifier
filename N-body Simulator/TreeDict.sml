structure TreeDict: LABDICT =
struct
	datatype (’k, ’v) tree =
		Empty
		| Node of (’k, ’v) tree * (’k * ’v) * (’k, ’v) tree

  	type ('k, 'v) dict = ('k, 'v) tree
  	val empty : ('k, 'v) tree = Empty
  	val insert : ('k * 'k -> order) -> ('k, 'v) tree -> ('k * 'v) -> ('k, 'v) tree
  		fun insert cmp d (k,v) = 
  			case d of 
  				Empty => Node(Empty, (k,v), Empty)
  				| Node(l,(ks,vs),r) => case k > ks of
  					true => Node(l, (ks, vs), insert cmp r (k,v) )
  					false => Node (insert cmp l (k,v), (ks,vs), r)


  
end
