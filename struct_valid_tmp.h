#ifndef _VALID_STRUCT_H
#define _VALID_STRUCT_H  
//#include <stdlib.h>
#endif

extern const size_t DEFAULT_SIZE;
//@ predicate default_size_inv(size_t ds) = ds == 100;


typedef enum {go, stop } Memory_types;

struct Memory{
  int which ;
  struct Memory *ptr;
  int i;
};
typedef struct Memory Memory;

typedef struct TreeWalk TreeWalk;

struct TreeWalk{
  TreeWalk *p_left, *p_right, *p_parent;
  int info, key, depth, weight;
};

void struct_change_nothing1(Memory*);
void struct_change_nothing2(Memory*);


/*@ axiomatic struct_valid { 
  @    predicate valid_Memory_ptr{L}(Memory *k);
  @
  @    predicate valid_Memory{L}(Memory k)=
  @       (k.which==go || k.which==stop) &&
  @       (k.which==go ==> valid_Memory_ptr{L}(k.ptr)) &&
  @       (k.which==stop ==> valid_Memory_ptr{L}(k.ptr));
  @
  @ axiom valid_Memory_ptr_def{L}: \forall Memory *k; 
  @         valid_Memory_ptr{L}(k) <==> \valid{L}(k) && valid_Memory{L}(*k);
  @ } //struct_valid
  @
  @ lemma valid_ptr_to_valid{L}: \forall Memory *k;
  @        valid_Memory_ptr{L}(k) ==> \valid{L}(k);
  @
  @*/



/*@ axiomatic TreeWalk_valid { 
  @    predicate valid_TreeWalk_ptr{L}(TreeWalk *k);
  @
  @    predicate valid_TreeWalk{L}(TreeWalk k)=
  @       (k.p_parent != \null ==> valid_TreeWalk_ptr{L}(k.p_parent)) &&
  @       (k.p_left != \null ==> valid_TreeWalk_ptr{L}(k.p_left)) &&
  @       (k.p_right != \null ==> valid_TreeWalk_ptr{L}(k.p_right));
  @
  @ axiom valid_TreeWalk_ptr_def{L}: \forall TreeWalk *k; 
  @         valid_TreeWalk_ptr{L}(k) <==> \valid{L}(k) && valid_TreeWalk{L}(*k);
  @ } //TreeWalk_valid
  @
  @ lemma valid_TreeWalk_ptr_to_valid{L}: \forall TreeWalk *k;
  @        valid_TreeWalk_ptr{L}(k) ==> \valid{L}(k);
  @
  @*/

/*@ axiomatic Ax_TreeWalk_Exists_Value { 
  @    predicate TreeWalk_Exists_Value{L}(TreeWalk *k, int val)=
  @               (k!=\null && valid_TreeWalk_ptr{L}(k) && 
  @               (k->key == val || TreeWalk_Exists_Value{L}(k->p_left,val) ||
  @                                 TreeWalk_Exists_Value{L}(k->p_right,val))); 
  @   
  @    predicate TreeWalk_Exists_Value_Count{L}(TreeWalk *k, int val, int n)= (k==\null && n==0) ||
  @             (
  @		k!=\null && valid_TreeWalk_ptr{L}(k) && 
  @             	(
  @			
  @			( k->key != val && \exists int i, int j; 0<=i<=n && 0<=j<=n && i+j==n &&
  @			TreeWalk_Exists_Value_Count{L}(k->p_left,val,i) && TreeWalk_Exists_Value_Count{L}(k->p_right,val,j) )
  @			||
  @			( k->key == val && \exists int i, int j; 0<=i<=(n-1) && 0<=j<=(n-1) && i+j==(n-1) && 
  @			TreeWalk_Exists_Value_Count{L}(k->p_left,val,i) && TreeWalk_Exists_Value_Count{L}(k->p_right,val,j) )
  @
  @			)
  @
  @		);
  @
  @ } //Ax_TreeWalk_Exists_Value
  @
  @ lemma TreeWalk_NoValue_In_Null_Tree{L}: 
  @             \forall int v; ! TreeWalk_Exists_Value{L}(\null,v);
  @
  @ lemma TreeWalk_Exists_Value_Recursive{L}:
  @              \forall TreeWalk *k, int v;
  @               (valid_TreeWalk_ptr{L}(k) ==> 
  @        (TreeWalk_Exists_Value{L}(k,v) <==> ((k!=\null) && 
  @						((k->key==v)||
  @                                             TreeWalk_Exists_Value{L}(k->p_left,v)||    
  @                                             TreeWalk_Exists_Value{L}(k->p_right,v)))));
  @
  @ lemma TreeWalk_Zero_Values_In_Null_Tree{L}:
  @ 	\forall int v, int z; z==0 ==> TreeWalk_Exists_Value_Count{L}(\null,v,z);
  @	
  @ lemma TreeWalk_Exists_Value_Count_Recursive{L}:
  @              \forall TreeWalk *k, int v, int n;
  @              (   valid_TreeWalk_ptr{L}(k) ==> 
  @        (  TreeWalk_Exists_Value_Count{L}(k,v,n) <==> ((k==\null && n==0) || ((k!=\null) && 
  @			(
  @			
  @			( k->key != v && \exists int i, int j; 0<=i<=n && 0<=j<=n && i+j==n &&
  @			TreeWalk_Exists_Value_Count{L}(k->p_left,v,i) && TreeWalk_Exists_Value_Count{L}(k->p_right,v,j) )
  @			||
  @			( k->key == v && \exists int i, int j; 0<=i<=(n-1) && 0<=j<=(n-1) && i+j==(n-1) && 
  @			TreeWalk_Exists_Value_Count{L}(k->p_left,v,i) && TreeWalk_Exists_Value_Count{L}(k->p_right,v,j) )
  @
  @			)))  )   );
  @
  @
  @
  @
  @
  @
  @
  @
  @
  @
  @
  @								
  @*/
