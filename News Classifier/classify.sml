
functor NaiveBayes (ClassSpec : sig
                                  structure Category : ORDERED
                                  val default_category : Category.t
                                      
                                  structure Dataset : MAP_REDUCE
                                end) : NAIVE_BAYES_CLASSIFIER =
struct

    type category = ClassSpec.Category.t

    type labeled_document = category * string Seq.seq
    type document = string Seq.seq

    structure Dataset = ClassSpec.Dataset

    (* TASK instantiate the ExtractCombine functor 3 times, and 
            define CatDict and WordDict and CatWordDict 
            to be the dictionary modules this produces
    *)









    structure CatEC = ExtractCombine(struct
                                        structure Key = ClassSpec.Category
                                        structure MR = ClassSpec.Dataset
                                    end)
    structure WordEC = ExtractCombine(struct
                                        structure Key = StringLt
                                        structure MR = ClassSpec.Dataset
                                      end)
    
    structure CatWordEC = ExtractCombine(struct
                                          structure Key = PairOrder(struct
                                                                      structure O1 =  ClassSpec.Category
                                                                      structure O2 = StringLt
                                                                    end)
                                          structure MR = ClassSpec.Dataset
                                        end)

    structure CatDict = CatEC.D
    structure WordDict = WordEC.D
    structure CatWordDict = CatWordEC.D


    

    type statistics = 
          int CatDict.dict     (* maps each category to number of documents with that category *)
        * int CatDict.dict     (* maps each category to number of words in documents with that category *)
        * int CatWordDict.dict (* maps each (cat,word) to frequency *)
        * category Seq.seq     (* list of categories (no duplicates) *)
        * int                  (* total number of documents *)
        * int                  (* total number of different words *)

    
        

    (* TASK *)
    fun gather (train : labeled_document Dataset.mapreducable) : statistics = 
      (*argument: dataset of labeled documents*)
      let val num_docs_by_cat = CatEC.extractcombine(fn (cat, words) => Seq.singleton(cat, 1) ) (fn (count1, count2) => (count1 + count2)) train

          val num_words_by_cat = CatEC.extractcombine(fn (cat, words) =>  Seq.singleton(cat, Seq.length(words))) (fn (count1, count2) => (count1 + count2)) train

          val freqs = CatWordEC.extractcombine(fn (cat, words) => Seq.map (fn w => ((cat, w), 1)) words )  (fn (count1, count2) => (count1 + count2)) train 

              (* creates dict with cat,word,int*)

          val all_categories = Seq.map (fn (cat,words) => cat) (CatDict.toSeq num_docs_by_cat)

          val total_num_docs = Seq.mapreduce (fn (cat,num) => num) 0 (fn (c1, c2) => c1 + c2) (CatDict.toSeq num_docs_by_cat)

         val total_num_words = WordDict.size (WordEC.extractcombine (fn (cat, words) => Seq.map (fn w => (w, ())) words )  (fn (x,y) => () ) train ) 
              (* why does this make sense?*)
          
        in
          (num_docs_by_cat, num_words_by_cat, freqs, all_categories, total_num_docs, total_num_words )
        end

        
        
    (* TASK *)
    fun possible_classifications 
        ((num_docs_by_cat,
          num_words_by_cat,
          freqs,
          all_categories, 
          total_num_docs,
          total_num_words) : statistics)
        (test_doc : document) : (category * real) Seq.seq = 

           Seq.map (fn cat => 
            let val num_docs_in_C = case CatDict.lookup num_docs_by_cat cat of
              NONE => 0
              |SOME(y) => y
              val total_words_in_C = case CatDict.lookup num_words_by_cat cat of
                NONE => 0
                |SOME(y) => y 
              val part1 =Math.ln( Real.fromInt(num_docs_in_C) / Real.fromInt (total_num_docs ))

              val part2 = Seq.mapreduce (fn w => case CatWordDict.lookup freqs (cat, w) of
                          NONE => Math.ln (1.0 / Real.fromInt(total_num_words))
                         | SOME (y) => Math.ln (Real.fromInt(y)/ Real.fromInt (total_words_in_C))) (0.0)
                      (fn (c1,c2) => c1+c2) test_doc
            in
              (cat, part1 + part2)
            end)
            all_categories
                

    (* TASK *)
    fun classify (stats : statistics)
                 (test_doc : document) : (category * real) = 
              let val probabilities_seq = possible_classifications stats test_doc
              in 

                Seq.reduce (fn ((cat_1, c1) ,(cat_2, c2)) => case Real.compare(c1,c2) of
                  EQUAL => (cat_1, c1)
                  |LESS => (cat_2, c2)
                  |GREATER => (cat_1, c1)
                  ) (ClassSpec.default_category , Real.negInf) probabilities_seq
              end

    (* TASK *)
    fun train_classifier (train : labeled_document Dataset.mapreducable) : document -> (category * real) =
      let val stats = gather train
        in
            fn doc => classify stats doc
        end


   
        
end

(*Report:
small: (5,8) = 62.5%
medium: (680,808) = 84.2%
large:  (70122,78899) = 88.9%  

big training data medium test: (704,808) = 87.1%

*)
