datatype Tree<T> = Leaf | Node(Tree<T>, Tree<T>, T)
datatype List<T> = Nil | Cons(T, List<T>)

function flatten<T>(tree:Tree<T>):List<T>
{
	match(tree)
		case Leaf => Nil
		case Node(treeLeft, treeRight, head) => Cons(head, append(flatten(treeLeft), flatten(treeRight)))
}

function append<T>(xs:List<T>, ys:List<T>):List<T>
{
	match(xs)
		case Nil => ys
		case Cons(x, xs') => Cons(x, append(xs', ys))	
}

function treeContains<T>(tree:Tree<T>, element:T):bool
{
	match(tree)
		case Leaf => false
		case Node(treeLeft, treeRight, head) => (head == element) || treeContains(treeLeft, element) || treeContains(treeRight, element)
}

function listContains<T>(xs:List<T>, element:T):bool
{
	match(xs)
		case Nil => false
		case Cons(x, xs') => (x == element) || listContains(xs', element)
}

lemma listContainsWithAppend<T>(xs:List<T>, ys:List<T>, element:T)
ensures (listContains(xs, element) || listContains(ys, element)) == listContains(append(xs,ys), element)
{

}

lemma sameElements<T>(tree:Tree<T>, element:T)
ensures treeContains(tree, element) <==> listContains(flatten(tree), element)
{

	match(tree)
		case Leaf => {
		}

		case Node(treeLeft, treeRight, head) => {

			listContainsWithAppend(flatten(treeLeft), flatten(treeRight), element); //lemma used
			assert(   treeContains(tree, element) 
				   ==  treeContains(Node(treeLeft, treeRight, head), element) 
				   == ((head == element) || treeContains(treeLeft, element) || treeContains(treeRight, element)) 
				   == ((head == element) || (listContains(flatten(treeLeft), element) || listContains(flatten(treeRight), element))) //by IH
				   == ((head == element) || (listContains(append(flatten(treeLeft), flatten(treeRight)), element)))                  //by lemma called above
				   == (listContains(Cons(head, append(flatten(treeLeft), flatten(treeRight))), element)) //next steps were not necessary for dafny to be happy but included anyways
				   == (listContains(flatten(Node(treeLeft, treeRight, head)), element)) 
				   == (listContains(flatten(tree), element))
		    );
			
		}
}

