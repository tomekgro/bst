#include <stdlib.h>
#include <stdio.h>
#include <stdbool.h>
#include <string.h>
#include <assert.h>

#include "struct_valid_tmp.h"

void struct_change_nothing1(Memory*);
void struct_change_nothing2(Memory*);

/*@ requires \valid(k) && valid_Memory_ptr(k);
  @ assigns \nothing;
  @*/

void struct_change_nothing1(Memory *k){
  if(k==NULL)
    return;
  else {
     if(k->which == go)
      struct_change_nothing1(k->ptr);
  }
}

/*@ requires valid_Memory_ptr(k);
  @ assigns \nothing;
  @*/

void struct_change_nothing2(Memory *k){
  if(k==NULL)
    return;
  else
    if(k->which == go)
      struct_change_nothing2(k->ptr);
}

/*@ requires \valid(k) && valid_TreeWalk_ptr(k);
  @ assigns \nothing;
  @*/

void TreeWalk_change_nothing(TreeWalk *k){
  if(k==NULL)
    return;
  else {
     if(k->left == go)
      TreeWalk_change_nothing(k->p_left);
     if(k->right==go)
       TreeWalk_change_nothing(k->p_right);
  }
}



/*@ requires \valid(k) && valid_TreeWalk_ptr(k);
  @ assigns \nothing;
  @*/

void TreeWalk_change_nothing_DownAndUp(TreeWalk *k, int Upwards){

    switch (Upwards)
    {
      case 0:
        if(k==NULL)
          return;
        else {
          if(k->left == go)
            TreeWalk_change_nothing_DownAndUp(k->p_left,0);
          else TreeWalk_change_nothing_DownAndUp(k,1);
          if(k->right == go)
            TreeWalk_change_nothing_DownAndUp(k->p_right,0);
          else TreeWalk_change_nothing_DownAndUp(k,1);
          }
        break;

      case 1:
        if(k==NULL) return;
       else
         {
         if(k->up == go) TreeWalk_change_nothing_DownAndUp(k->p_parent,1);
         }
       break;
    }
}



/*@ requires \valid(k) && valid_TreeWalk_ptr(k);
  @ assigns \nothing;
  @*/

void TreeWalk_change_nothing_with_case(TreeWalk *k){
  if(k==NULL)
    return;
  if(k->left == go)
     TreeWalk_change_nothing(k->p_left);
  if(k->right==go)
       TreeWalk_change_nothing(k->p_right);
}


/*@ requires valid_Memory_ptr(k);
  @ assigns \nothing;
  @*/
void struct_recursion_simple(Memory *k){
  //if(k==NULL)
  //return;
  if(k->which == go)
    return;
  if(k->which==stop)
    return;
}
