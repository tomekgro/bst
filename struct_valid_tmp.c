#include <stdlib.h>
#include <stdio.h>
#include <stdbool.h>
#include <string.h>
#include <assert.h>

#include "struct_valid_tmp.h"

void struct_change_nothing1(Memory*);
void struct_change_nothing2(Memory*);

void multi_insert(TreeWalk *, TreeWalk *);
TreeWalk *get_TreeWalk();
int CountVal(TreeWalk *, int, int);
void updatedepth (TreeWalk *);


TreeWalk *root;
int appears;

void main()
{
   int choice,ptrcounter;
   int searchedkey, deletedkey;
   TreeWalk *new_TreeWalk;
   root = NULL;
   int leftdepth, rightdepth;
   do
   {  

	scanf("%d", &choice);

	switch (choice)
	{
		case 1: // We create a new node and make it a root if the tree was empty or use the function 'multi_insert'.
			new_TreeWalk = get_TreeWalk();
			scanf("%d", &new_TreeWalk->key);
			if (root == NULL) /* tree was empty */
			{
				root = new_TreeWalk;
			}
			else multi_insert(root, new_TreeWalk);
			break;
	
		case 2:
			scanf("%d", &searchedkey);
			appears = CountVal(root,searchedkey,0);
			printf("\nThe given value appears ");
			printf("%d", appears);
			printf(" time(s) in the requested tree.");
			break;
	
   	}

   } while (choice != 0);
}
// FUNCTIONS FROM BSTTG

/* getiing a new node  */
TreeWalk *get_TreeWalk()
{
	TreeWalk *temp;
	temp = (TreeWalk *) malloc(sizeof(TreeWalk));
	temp->p_left = NULL;
	temp->p_right = NULL;
	temp->p_parent = NULL;
	temp->depth = 0;
	temp->weight = 0;
	return temp;
}

/* inserting a node to an existing tree, multiple version */

/*@ requires \valid(root) && valid_TreeWalk_ptr(root) && \valid(new_TreeWalk) && valid_TreeWalk_ptr(new_TreeWalk);
  @ assigns \nothing;
  @*/

void multi_insert(TreeWalk *root, TreeWalk *new_TreeWalk)
{
	if (new_TreeWalk->key < root->key)
	{
		if (root->p_left == NULL)
		{
			root->p_left = new_TreeWalk;
			new_TreeWalk->p_parent = root;
			updatedepth(root); // Updates the depth of every node above the inserted node.
		}
		else multi_insert(root->p_left, new_TreeWalk);
	}

	else if (new_TreeWalk->key >= root->key)
	{
        	if (root->p_right == NULL)
        	{
		root->p_right = new_TreeWalk;
        	new_TreeWalk->p_parent = root;
	        updatedepth(root); // Updates the depth of every node above the inserted node.
		}		
        	else multi_insert(root->p_right, new_TreeWalk);
	}

}

/* @ requires \valid(root) && valid_TreeWalk_ptr(root);
   @ assigns \nothing;
   @ */

void updatedepth(TreeWalk *root) // It starts with the given node and goes upwards, to the root - updating each depth.
{
	TreeWalk *temp;
	temp = root;
	while (temp != NULL)
	{
		if (temp->p_left == NULL && temp->p_right == NULL) temp->depth = 0;
		else if (temp->p_left == NULL) temp->depth = (temp->p_right->depth +1);
		else if (temp->p_right == NULL) temp->depth = (temp->p_left->depth +1); 
		else if (temp->p_left->depth > temp->p_right->depth) temp->depth = (temp->p_left->depth +1);
		else temp->depth = (temp->p_right->depth +1);
		temp = temp->p_parent;

	}
}



// FUNCTIONS FROM STRUCT_VALID_TMP


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
     if(k->p_left != NULL)
      TreeWalk_change_nothing(k->p_left);
     if(k->p_right != NULL)
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
        if(k==NULL){
          //TreeWalk_change_nothing_DownAndUp(k->p_parent,1);
          return;
            }
        else {
          if(k->p_left != NULL)
            TreeWalk_change_nothing_DownAndUp(k->p_left,0);
          if(k->p_right != NULL)
            TreeWalk_change_nothing_DownAndUp(k->p_right,0);
          }
        break;

      case 1:
        if(k==NULL)  {return;}
       else
         {
         if(k->p_parent != NULL)
         TreeWalk_change_nothing_DownAndUp(k->p_parent,1);
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
  if(k->p_left != NULL)
     TreeWalk_change_nothing(k->p_left);
  if(k->p_right != NULL)
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


/*@ requires \valid(p) && valid_TreeWalk_ptr(p) && \valid(root) && valid_TreeWalk_ptr(root);
  @ assigns \nothing;
  @*/

int CountPtr(TreeWalk *root, TreeWalk *p, int n)
{
        int counter;
        counter = n;
        if (root == NULL) return counter;
        else
        {
          counter = CountPtr(root->p_left,p,counter);
          if (root == p && counter<100) counter = counter+1;
          counter = CountPtr(root->p_right,p,counter);
        }
        return counter;
}

/*@ requires \valid(root) && valid_TreeWalk_ptr(root) && n<=100;
  @
  @ assigns \nothing;
  @
  @ ensures \result <=100;
  @
  @ ensures \forall int m; (m == 100) ==> \result <=m;
  @
  @ ensures \forall int m; (m == 1) ==> ((\result == n+m) ==> TreeWalk_Exists_Value_Count(root,val,m)); 
  @
  @ ensures \forall int m; (m == 1 && \result == n+m) ==> root != \null;
  @
  @ ensures \forall int m; (m > 0 && \result == n+m) ==> root != \null;
  @
  @ ensures \forall int m; ((m == 0) && TreeWalk_Exists_Value_Count(root,val,m)) ==> 
  @	(  root ==\null || ( root!=\null && root->key != val && (TreeWalk_Exists_Value_Count(root->p_left,val,m)) && 
  @	TreeWalk_Exists_Value_Count(root->p_right,val,m) )  );
  @
  @ ensures \forall int m; ((m == 0) && TreeWalk_Exists_Value_Count(root,val,m) &&
  @	root != \null && TreeWalk_Exists_Value_Count(root->p_left,val,m) && TreeWalk_Exists_Value_Count(root->p_right,val,m) &&
  @	root->key != val ) ==> (\result == n);
  @
  @ ensures \forall int m; (m==0 && TreeWalk_Exists_Value_Count(root,val,m))==> \result == n;
  @
  @ ensures \forall int m, int z; ( m == 1 && z == 0 && TreeWalk_Exists_Value_Count(root,val,m) ) ==> root != \null &&
  @	((root->key != val && TreeWalk_Exists_Value_Count(root->p_left,val,m) && TreeWalk_Exists_Value_Count(root->p_right,val,z) ) ||
  @	(root->key != val && TreeWalk_Exists_Value_Count(root->p_left,val,z) && TreeWalk_Exists_Value_Count(root->p_right,val,m) ) ||
  @	(root->key == val && TreeWalk_Exists_Value_Count(root->p_left,val,z) && TreeWalk_Exists_Value_Count(root->p_right,val,z) )
  @	);
  @
  @ ensures \forall int m, int l, int r; (l >= 0 && r >= 0 && m == 2 && m == l+r && root != \null &&
  @	root->key != val && TreeWalk_Exists_Value_Count(root->p_left,val,l) && TreeWalk_Exists_Value_Count(root->p_right,val,r) ) ==>
  @	TreeWalk_Exists_Value_Count(root,val,m);
  @
  @ ensures \forall int m, int l, int r; (l >= 0 && r >= 0 && m == 3 && m == l+r && root != \null &&
  @	root->key != val && TreeWalk_Exists_Value_Count(root->p_left,val,l) && TreeWalk_Exists_Value_Count(root->p_right,val,r) ) ==>
  @	TreeWalk_Exists_Value_Count(root,val,m);
  @
  @ ensures \forall int m, int l, int r; (l >= 0 && r >= 0 && m < 100 && m == l+r && root != \null &&
  @	root->key != val && TreeWalk_Exists_Value_Count(root->p_left,val,l) && TreeWalk_Exists_Value_Count(root->p_right,val,r) ) ==>
  @	TreeWalk_Exists_Value_Count(root,val,m);
  @
  @ ensures \forall int m, int l, int r; (l >= 0 && r >= 0 && m < 100 && m == l+r && root != \null &&
  @	root->key != val && TreeWalk_Exists_Value_Count(root->p_left,val,l) && TreeWalk_Exists_Value_Count(root->p_right,val,r) ) ==>
  @	\result == n+m;
  @
  @ ensures \forall int m; (m==1 && TreeWalk_Exists_Value_Count(root,val,m)) ==> \result == n+m;
  @
  @ ensures \forall int m, int l, int r; (l >= 0 && r >= 0 && m == 1 && m == l+r && root != \null &&
  @	root->key != val && TreeWalk_Exists_Value_Count(root->p_left,val,l) && TreeWalk_Exists_Value_Count(root->p_right,val,r) ) ==>
  @	\result == n+m;
  @ 
  @ ensures \forall int m, int l, int r; (l >= 0 && r >= 0 && m == 1 && m == l+r && root != \null &&
  @	root->key == val && TreeWalk_Exists_Value_Count(root->p_left,val,l) && TreeWalk_Exists_Value_Count(root->p_right,val,r) ) ==>
  @	\result == n+m+1;
  @
  @ ensures \forall int m, int l, int r; (l >= 0 && r >= 0 && m == 2 && m == l+r && root != \null &&
  @	root->key != val && TreeWalk_Exists_Value_Count(root->p_left,val,l) && TreeWalk_Exists_Value_Count(root->p_right,val,r) ) ==>
  @	\result == n+m;
  @*/

int CountVal(TreeWalk *root, int val, int n)

{
        int counter;
        counter = n;
        if (root == NULL) return counter;
	else
        {
          if (root->p_left != NULL) counter = CountVal(root->p_left,val,counter);
          if (root->key == val && counter<100) counter = counter+1;
          if (root->p_right != NULL) counter = CountVal(root->p_right,val,counter);
        }
        return counter;
}

