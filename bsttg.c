#include <stdio.h>
#include <stdlib.h>
// I am writing this comment to check if everything works.
typedef struct BST
{
	int key;
	int depth, weight;
	struct BST *left, *right, *p;
} node;

int appears, doesntappear, deleted;

node *root;

//headers
void insert(node *, node *);
node *get_node();
int search(node *, int);
void deletekey (node **, int);
void deletenode (node **);
void updatedepth (node *);
void increasing_list (node *);
void inorder_tree_walk (node *);
void list_along_branches (node *);
void preorder_tree_walk (node *);

void main()
{
   int choice;
   int searchedkey, deletedkey;
   node *new_node;
   root = NULL;
   int leftdepth, rightdepth;
   do
   {  

	printf("\nBinary Search Trees");
	printf("\n1. Insert");
	printf("\n2. Check");
	printf("\n3. Delete");
	printf("\n4. Balance a bit");
	printf("\n5. Balance the root totally");
	printf("\n6. Show the root and its sons");
	printf("\n7. Show the root's depth");
	printf("\n8. Show the increasing list of elements.");
	printf("\n9. Show the list of elements along the branches.");
	printf("\n0. Exit");
	scanf("%d", &choice);

	switch (choice)
	{
		case 1: // We create a new node and make it a root if the tree was empty or use the function 'insert'.
			new_node = get_node();
			printf("\nEnter the element to be inserted.");
			scanf("%d", &new_node->key);
		
			if (root == NULL) /* tree was empty */
			{
				root = new_node;
			}
			else insert(root, new_node);
			break;
	
		case 2:
			printf("Enter the element to be searched.");
			scanf("%d", &searchedkey);
			appears = search(root, searchedkey);
			if (appears == 1) printf("\nYES, the given element appears in the tree.");
			else printf("\nNO, the give element doesn't appear in the tree.");
			break;
	
		case 3: // Deletes a node with the given key, putting in its place the right of the left son - the one with a bigger depth. By depth I mean the number of levels below an element.
			printf("\nEnter the element to be deleted.");
			scanf("%d", &deletedkey);
			deletekey(&root, deletedkey);
			printf("The given element has been deleted.");
			break;
	
		case 4: // Deletes and inserts the key of the root in order to reduce by one the difference between depths of the left and the right subtree of the root.
			deletedkey = root->key;
			deletekey(&root, deletedkey);
			new_node = get_node();
			new_node->key = deletedkey;
			if (root == NULL)
			{
				root = new_node;
			}
			else insert(root, new_node);
			break;
		
		case 5: // Repeats the above step until the depths of the left and right subtree of the root differ at most by one.
			if (root->left == NULL) leftdepth = 0;
			else leftdepth = (root->left->depth +1);
			if (root->right == NULL) rightdepth = 0;
			else rightdepth = (root->right->depth +1);

			if (root == NULL);
			else while (rightdepth - leftdepth != 0 && rightdepth - leftdepth != 1 && rightdepth - leftdepth != -1)
			{
 				deletedkey = root->key;
                		deletekey(&root, deletedkey);
				new_node = get_node();
        	        	new_node->key = deletedkey;
                		insert(root, new_node);
			
				if (root->left == NULL) leftdepth = 0;
	               		else leftdepth = (root->left->depth+1);
        	        	if (root->right == NULL) rightdepth = 0;
           			else rightdepth = (root->right->depth+1);
			} 
			printf("\nThe root has been balanced.");
			break;
	
		case 6: // Prints the first two levels of the tree- nothing important, actually.
			if (root == NULL) printf("\nThe tree is empty.");
			else 
			{
				printf("\nThe root is ");
				printf("%d", root->key);
				if (root->left == NULL) printf("\nThe root's left son is NULL.");
				else
				{
					printf("\nThe left son is ");
					printf("%d", root->left->key);
				}
				if (root->right == NULL) printf("\nThe root's right son is NULL");
				else
				{
                       			printf("\nThe right son is ");
                      			printf("%d", root->right->key);
                       		}
			}
			break;
	
		case 7: 
			if (root == NULL) printf("The tree is empty.");
			else if (root->depth == 1) printf("\nThere is 1 level below the root.");
			else 
			{
				printf("\nThere are ");
				printf("%d", root->depth);
				printf(" levels below the root.");	
			}
			break;
		case 8:
			if (root == NULL) printf("\n The tree is empty.");
			else increasing_list(root);
			break;

		case 9:
			if (root == NULL) printf("\n The tree is empty.");
			else list_along_branches(root);
			break;
	}
		
   } while (choice != 0);

}





//@@@  FUNCTIONS @@@

/* getiing a new node  */
node *get_node()
{
	node *temp;
	temp = (node *) malloc(sizeof(node));
	temp->left = NULL;
	temp->right = NULL;
	temp->p = NULL;
	temp->depth = 0;
	temp->weight = 0;
	return temp;
}



/* inserting a node to an existing tree */
void insert(node *root, node *new_node)
{
	if (new_node->key < root->key)
	{
		if (root->left == NULL)
		{
			root->left = new_node;
			new_node->p = root;
			updatedepth(root); // Updates the depth of every node above the inserted node.
		}
		else insert(root->left, new_node);
	}

	else if (new_node->key > root->key)
	{
        	if (root->right == NULL)
        	{
		root->right = new_node;
        	new_node->p = root;
	        updatedepth(root); // Updates the depth of every node above the inserted node.
		}		
        	else insert(root->right, new_node);
	}

	else /*(new_node->key == root->key)*/ printf("\nInserted key already appears in the tree. It was NOT inserted for the second time.");
}



/* checking if the given key appears in the tree with a given root and returning YES/NO answer */
int search(node *root, int searchedkey)
{
	node *temp;
	temp = root;
	appears = 0; // Controls the apprearance
	while (appears == 0 && temp != NULL) 
	{
		if (temp->key == searchedkey) appears = 1;
		else if (temp->key > searchedkey) temp = temp->left;
		else temp = temp->right;
	} 
	return appears;
}



/* deleting a node with the given key */
void deletekey (node **rootpointer, int deletedkey) // Finds a node with a given key in the tree with a root *rootpointer and runs the function "deletenode".
{
	node *temp;
	node *parent;
	parent = NULL;
	temp = *rootpointer;
	deleted = 0;

	if ((*rootpointer)->key == deletedkey) 
	{
		deletenode(rootpointer);
		deleted = 1;
	}		

	else if ((*rootpointer)->key > deletedkey && deletedkey == (*rootpointer)->left->key)
	{
		deletenode(&(*rootpointer)->left);
		deleted = 1;
	}

	else if ((*rootpointer)->key < deletedkey && deletedkey == (*rootpointer)->right->key)
	{
		deletenode(&(*rootpointer)->right);
		deleted = 1;
	}

	else
	{
		while (deleted == 0 && temp != NULL) 
		{
			if (temp->key > deletedkey) 
			{
				parent = temp;
				temp = temp->left;
			}
			else if (temp->key < deletedkey)
			{
				parent = temp;
				temp = temp->right;
			}
			else /* temp->key == deletedkey */
			{
				if (deletedkey == parent->left->key) deletenode(&parent->left);
				else deletenode(&parent->right);
				deleted = 1;
			}
		}
	}

	if (deleted == 0) printf("\nThe given key doesn't appear in the tree. It was NOT deleted.");
}



void deletenode (node **deletedroot) // Deletes a given node. "deletedroot" is an address of a pointer to a deleted root.
{
	node *temp;
	node *parent;
	if ((*deletedroot)->left == NULL && (*deletedroot)->right == NULL)
	{
		free(*deletedroot);
		*deletedroot = NULL;
	}
	else if ((*deletedroot)->left == NULL)
	{
		temp = (*deletedroot)->right;
		free(*deletedroot);
		temp->p = NULL;
		*deletedroot = temp;
		//No change of depths is needed.
	}
	else if ((*deletedroot)->right == NULL)
	{
		temp = (*deletedroot)->right;
		free(*deletedroot);
		temp->p = NULL;
		*deletedroot = temp;
		//No change of depths is needed.
	}
	else // Both sons of *deletedroot are not NULL
	{	

		if ((*deletedroot)->left->depth > (*deletedroot)->right->depth) // The left son of *deletedroot will be a new root.
		{
			if ((*deletedroot)->left->right == NULL) 
			{
				(*deletedroot)->left->right = (*deletedroot)->right;
				(*deletedroot)->right->p = (*deletedroot)->left;
				temp = (*deletedroot)->left;
				free(*deletedroot);
				temp->p = NULL;
				updatedepth(temp); //Updates the depth of temp. whicn is a new root 
				*deletedroot = temp;
			}
			else
			{
				parent = (*deletedroot)->left;
				temp = parent->right;
				while (temp->right != NULL)
				{
					parent = temp;
					temp = temp->right;
				} /* temp now points a node with the biggest key in a left subtree of *deletedroot - a new root */
				temp->right = (*deletedroot)->right;
				(*deletedroot)->right->p = temp;
				parent->right = temp->left;
				if (temp->left != NULL) temp->left->p = parent;
				temp->left = (*deletedroot)->left;
				(*deletedroot)->left->p = temp;
				free(*deletedroot);
				temp->p = NULL;
				updatedepth(parent);
				updatedepth(temp);
				*deletedroot = temp; 
			}
		}

		else // root->right is a default new root. Analogously as above.
        	{
            		if ((*deletedroot)->right->left == NULL)
			{	
                		(*deletedroot)->right->left = (*deletedroot)->left;
				(*deletedroot)->left->p = (*deletedroot)->right;
				temp = (*deletedroot)->right;
				free(*deletedroot);
				temp->p = NULL;
                		*deletedroot = temp;
				updatedepth(temp);
			}
            		else
            		{
                		parent = (*deletedroot)->right;
		                temp = parent->left;
                		while (temp->left != NULL)
                		{
                    			parent = temp;
                    			temp = temp->left;
		                } /* temp now points the new root */
        	        	temp->left = (*deletedroot)->left;
				(*deletedroot)->left->p = temp;
               		 	parent->left = temp->right;
				if (temp->right != NULL) temp->right->p = parent;
				temp->right = (*deletedroot)->right;
				(*deletedroot)->right->p = temp;
				free(*deletedroot);
				temp->p = NULL;
				updatedepth(parent);
				updatedepth(temp);
	       		        *deletedroot = temp;
            		}
        	}
	}
}



void updatedepth(node *root) // It starts with the given node and goes upwards, to the root - updating each depth.
{
	node *temp;
	temp = root;
	while (temp != NULL)
	{
		if (temp->left == NULL && temp->right == NULL) temp->depth = 0;
		else if (temp->left == NULL) temp->depth = (temp->right->depth +1);
		else if (temp->right == NULL) temp->depth = (temp->left->depth +1); 
		else if (temp->left->depth > temp->right->depth) temp->depth = (temp->left->depth +1);
		else temp->depth = (temp->right->depth +1);
		temp = temp->p;
	}
}



void increasing_list(node *root) // Prints an increasing list of elements in the tree.
{
	printf("\nElements of the tree in an increasing order:\n"),
	inorder_tree_walk(root);
}


	
void inorder_tree_walk(node *root)
{	
	if (root != NULL)
	{
		inorder_tree_walk(root->left);
		printf("%d", root->key);
		printf(" ");
		inorder_tree_walk(root->right);
	}
}

void list_along_branches(node *root) //Preorder tree walk.
{
        printf("\nElements of the tree ordered along the branches:\n"),
        preorder_tree_walk(root);
}




void preorder_tree_walk(node *root)
{
	if (root != NULL)
	{
		printf("%d", root->key);
		printf(" ");
		preorder_tree_walk(root->left);
		preorder_tree_walk(root->right);
	}
}
