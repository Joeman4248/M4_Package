(* =========================================================================================================== *)
structure Model =

struct 

(* =========================================================================================================== *)
(* This function may be useful to get the leaf node of a tree -- which is always a string (even for integers).
   It is up to the interpreter to translate values accordingly (e.g., string to integer and string to boolean).
   
   Consult (i.e., open Int and open Bool) the SML structures Int and Bool for functions that can help with 
   this translation. 
*)
fun getLeaf( term ) = CONCRETE.leavesToStringRaw term 


(* For your typeChecker you may want to have a datatype that defines the types 
  (i.e., integer, boolean and error) in your language. *)
datatype types = INT | BOOL | ERROR;


(* It is recommended that your model store integers and Booleans in an internal form (i.e., as terms belonging to
   a userdefined datatype (e.g., denotable_value). If this is done, the store can be modeled as a list of such values.
*)
datatype denotable_value =  Boolean of bool 
                          | Integer of int;


type loc   = int
type env   = (string * types * loc) list     (* (id, type, location) *)
type store = (loc * denotable_value) list    (* (location, value) *)


(* The model defined here is a triple consisting of an environment, an address counter, and a store. The environment
   and the store are lists similar to what we have used in class. The address counter serves as an implementation of
   new(). Note that, depending on your implementation, this counter either contains the address of (1) the
   next available memory location, or (2) the last used memory location -- it all depends on when the counter is 
   incremented. *)
val initialModel = ( []:env, 0:loc, []:store )

(* getLoc: environment → location *)
fun getLoc ( id, t, loc ) = loc   

(* getType: environment → type *)
fun getType( id, t, loc ) = t     

(* accessEnv: identifier * model → environment *)
fun accessEnv( id1, ([], _, _) ) = raise Fail("ERROR:" ^ id ^ "is undeclared in this scope!")
  | accessEnv( id1, ((id2, t, loc)::env, loc, store)) = 
      if (id1 = id2) then
         (id2, t, loc)
      else
         accessEnv(id1, (env, loc, store))

(* accessStore: location * model → value *)
fun accessStore( _, (_, _, []) ) = raise Fail("ERROR: uninitialized variable!")
  | accessStore( loc1, (env, loc, (loc2, v2)::store)) = 
      if (loc1 = loc2) then
         v2
      else
         accessStore(loc1, (env, loc, store))

(* updateEnv: id * type * model → model
 *    Instead of new(), we will use the address counter, 
 *    'loc' in the model to place a new environment tuple (id, type, loc) *)
fun updateEnv( id1, t1, (env, loc, store) ) = 
      let 
         fun new_env([]) = [(id1, t1, loc)]  (* if new id is not found in current env, 
                                              * add it (along with the new type & location) *)
           | new_env((id2, t2, loc2)::env2) = 
               if (id1 = id2) then
                  raise Fail("ERROR: " ^ id1 ^ " is already declared in this scope!")
               else
                  (id2, t2, loc2)::add_env(env2)
      in
         (new_env(env), loc + 1, store)
      end


(* updateStore: location * type * model → model 
 *    if the given location is present in the store, update the store,
 *    otherwise, add a new entry to the store.  *)
fun updateStore( loc1, v1, (env, loc, store) ) = 
      let
         fun new_store([]) = [(loc1, v1)]    (* add new entry *)
           | new_store((loc2, v2)::store) = 
               if (loc1 = loc2) then 
                  (loc1, v1)::store          (* replace existing entry *)
               else
                  (loc2, v2)::store
      in
         (env, loc, new_store(store))
      end



(* =========================================================================================================== *)
end; (* struct *) 
(* =========================================================================================================== *)
