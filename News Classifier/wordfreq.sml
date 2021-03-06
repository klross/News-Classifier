
structure WordFreq =
struct
    structure EC = ExtractCombine(struct structure Key = StringLt
                                         structure MR = SeqMR
                                  end)
    
    fun wordCounts (d : string Seq.seq) : int EC.D.dict =
        EC.extractcombine (fn s => Seq.map (fn w => (w, 1)) (SeqUtils.words s))
                          (op+) 
                          d

    (* convert the output to a key-value list for easy printing *)
    fun wordCounts_list (d : string Seq.seq) : (string * int) list = 
        Seq.tolist (EC.D.toSeq (wordCounts d))

    fun silToString(l : (string * int) list) : string =
        case l of
            [] => "[]"
          | (n,s) :: xs => "(" ^ n ^ "," ^ Int.toString s ^ ")" ^ "::" ^ silToString(xs)
                
    fun testsil (s : string) (n : (string * int) list) (m : (string * int) list) : unit =
        case n = m of
            true => print ("Test " ^ s ^ " OK\n")
          | false => print ("Test " ^ s ^ " FAILED:\n    Expected: " ^ silToString m ^ "\n    Got: " ^ silToString n ^ "\n")

    (*
    use this to test your extract_combine
    *)
        
    fun test() =
        testsil "fr" (wordCounts_list (Seq.fromlist ["this is is document 1",
                                                     "this is document 2"]))
                     [("1",1),("2",1),("document",2),("is",3),("this",2)] 

        
end
