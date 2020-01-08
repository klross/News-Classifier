
functor ExtractCombine (A : sig 
                                structure Key : ORDERED
                                structure MR : MAP_REDUCE
                            end) : EXTRACT_COMBINE =
struct
	structure MR = A.MR
	structure D = Dict(A.Key)

	 fun helper (s: (D.Key.t * 'v) Seq.seq) (combine : 'v * 'v -> 'v) : 'v D.dict=  
	 	let val extracter = fn (k,v) => D.insert D.empty (k,v)
	 		val combiner = fn(val_1,val_2) => D.merge combine (val_1,val_2)
	 	in (Seq.mapreduce extracter D.empty combiner s)
	 	end

	 fun extractcombine
	 	(extract: 'a -> (D.Key.t * 'v) Seq.seq )(combine: 'v * 'v -> 'v)
	 	(data: 'a MR.mapreducable) : 'v D.dict =

	 	let val extracter = fn a => helper (extract a) combine
	 		val combiner = fn (d1,d2) => D.merge combine (d1,d2)
	 	in (MR.mapreduce extracter D.empty combiner data)
	 	end
    
    
end

