signature Ordered = 
	sig
	  type t
	  val compare : t -> t -> int
	end

(*S Functional implementation. *)

signature FunctionalSig = 
	sig
	
		(* heap elements *)
 		type elt

  		(* Type of functional heaps *)
  		datatype t = 
	    	  Empty
	    	| FFF of t * elt * t (* full    (full,    full) *)
	    	| PPF of t * elt * t (* partial (partial, full) *)
	    	| PFF of t * elt * t (* partial (full,    full) *)
	    	| PFP of t * elt * t (* partial (full,    partial) *)

		exception EmptyHeap
			
	    (* The empty heap *)
	  	val empty : t
	
	  	(* [add x h] returns a new heap containing the elements of [h], plus [x];
	     complexity $O(log(n))$ *)
	  	val add : elt -> t -> t
	
	  	(* [maximum h] returns the maximum element of [h]; raises [EmptyHeap]
	     when [h] is empty; complexity $O(1)$ *)
	  	val maximum : t -> elt
	
	  	(* [remove h] returns a new heap containing the elements of [h], except
	     the maximum of [h]; raises [EmptyHeap] when [h] is empty; 
	     complexity $O(log(n))$ *) 
	  	val remove : t -> t
	
	  	(* usual iterators and combinators; elements are presented in
	     arbitrary order *)
	  	val iter : (elt -> unit) -> t -> unit
	
	  	val fold : (elt -> 'a -> 'a) -> t -> 'a -> 'a
	end

functor Functional (X : Ordered) : FunctionalSig = 
	struct

	  (* Heaps are encoded as complete binary trees, i.e., binary trees
	     which are full expect, may be, on the bottom level where it is filled 
	     from the left. 
	     These trees also enjoy the heap property, namely the value of any node 
	     is greater or equal than those of its left and right subtrees.
	
	     There are 4 kinds of complete binary trees, denoted by 4 constructors:
	     [FFF] for a full binary tree (and thus 2 full subtrees);
	     [PPF] for a partial tree with a partial left subtree and a full
	     right subtree;
	     [PFF] for a partial tree with a full left subtree and a full right subtree
	     (but of different heights);
	     and [PFP] for a partial tree with a full left subtree and a partial
	     right subtree. *)
	    

		type elt = X.t

		datatype t = 
	    	  Empty
	    	| FFF of t * elt * t (* full    (full,    full) *)
	    	| PPF of t * elt * t (* partial (partial, full) *)
	    	| PFF of t * elt * t (* partial (full,    full) *)
	    	| PFP of t * elt * t (* partial (full,    partial) *)
	    	
	    exception EmptyHeap

  		val empty = Empty
 
		(* smart constructors for insertion *)
  		fun p_f l x r = case l of
    		  Empty => PFF (l, x, r)
    		| FFF _ => PFF (l, x, r)
    		| _ => PPF (l, x, r)

  		fun pf_ l x l' = 
  			case l' of
  				  r as Empty => FFF (l, x, r)
  				| (r as FFF _)  => FFF (l, x, r)
    			| r => PFP (l, x, r)

		fun add x l' = 
	  		case l' of 
	  			  Empty => FFF (Empty, x, Empty)
	    		(* insertion to the left *)
	    		| FFF (l, y, r) =>
	    			if X.compare x y > 0 then p_f (add y l) x r else p_f (add x l) y r
	    		| PPF (l, y, r) =>
					if X.compare x y > 0 then p_f (add y l) x r else p_f (add x l) y r
	    		(* insertion to the right *)
	    		| PFF (l, y, r) =>
	    			if X.compare x y > 0 then pf_ l x (add y r) else pf_ l y (add x r)
	    		| PFP (l, y, r) =>
					if X.compare x y > 0 then pf_ l x (add y r) else pf_ l y (add x r)

  		fun maximum l = 
  			case l of
  				  Empty => raise EmptyHeap
    			| FFF (_, x, _) => x
    			| PPF (_, x, _) => x
    			| PFF (_, x, _) => x
    			| PFP (_, x, _) => x

  		(* smart constructors for removal; note that they are different
     		from the ones for insertion! *)
  		fun p_f l x r = case l of
    		  Empty => FFF (l, x, r)
    		| FFF _ => FFF (l, x, r)
    		| _ => PPF (l, x, r)

  		fun pf_ l x l' = case l' of
    		  r as Empty => PFF (l, x, r)
    		| r as FFF _ => PFF (l, x, r)
    		| r => PFP (l, x, r)

  		fun remove l'' = case l'' of
    		  Empty => raise EmptyHeap
    		| FFF (Empty, _, Empty) => Empty
    		| PFF (l, _, Empty) => l
    		(* remove on the left *)
    		| PPF (l, x, r) =>
    			let val xl = maximum l
					val xr = maximum r
					val l' = remove l 
				in
					if X.compare xl xr >= 0 then 
		  				p_f l' xl r 
					else 
		  				p_f l' xr (add xl (remove r))
		  		end
    		| PFF (l, x, r) =>
        		let val xl = maximum l
					val xr = maximum r
					val l' = remove l 
				in
					if X.compare xl xr >= 0 then 
		  				p_f l' xl r 
					else 
		  				p_f l' xr (add xl (remove r))
		  		end
    			(* remove on the right *)
    		| FFF (l, x, r) =>
    			let val xl = maximum l
					val xr = maximum r 
					val r' = remove r 
				in
					if (X.compare xl xr > 0) then 
		  				pf_ (add xr (remove l)) xl r'
					else 
		  				pf_ l xr r'
	  			end
    		| PFP (l, x, r) =>
        		let val xl = maximum l
					val xr = maximum r 
					val r' = remove r 
				in
					if (X.compare xl xr > 0) then 
		  				pf_ (add xr (remove l)) xl r'
					else 
		  				pf_ l xr r'
	  			end

  		fun iter f l' = 
  			case l' of
	    		  Empty => ()
	    		| FFF (l, x, r) => (iter f l; f x; iter f r)
	    		| PPF (l, x, r) => (iter f l; f x; iter f r)
	    		| PFF (l, x, r) => (iter f l; f x; iter f r)
	    		| PFP (l, x, r) => (iter f l; f x; iter f r)

  		fun fold f h x0 = case h of
  			  Empty => x0
    		| FFF (l, x, r) => fold f l (fold f r (f x x0))
    		| PPF (l, x, r) => fold f l (fold f r (f x x0))
    		| PFF (l, x, r) => fold f l (fold f r (f x x0))
    		| PFP (l, x, r) => fold f l (fold f r (f x x0))
	end