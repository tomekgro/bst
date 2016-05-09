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
  int left, right, up;
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
  @       (k.left==go || k.left==stop) && (k.right==go || k.right==stop)&&
  @       (k.up==go || k.up==stop)&&
  @       (k.up==go ==> valid_TreeWalk_ptr{L}(k.p_parent))&&
  @       (k.left==go ==> valid_TreeWalk_ptr{L}(k.p_left)) &&
  @       (k.right==go ==> valid_TreeWalk_ptr{L}(k.p_right))&&
  @       (k.left==stop ==> k.p_left==\null) &&
  @       (k.up==stop ==> k.p_parent==\null)&&
  @       (k.right==stop ==> k.p_right==\null);
  @
  @ axiom valid_TreeWalk_ptr_def{L}: \forall TreeWalk *k; 
  @         valid_TreeWalk_ptr{L}(k) <==> \valid{L}(k) && valid_TreeWalk{L}(*k);
  @ } //TreeWalk_valid
  @
  @ lemma valid_TreeWalk_ptr_to_valid{L}: \forall TreeWalk *k;
  @        valid_TreeWalk_ptr{L}(k) ==> \valid{L}(k);
  @
  @*/
