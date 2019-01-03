package ss.week4;

public class LinkedList<Element> {

    private /*@ spec_public @*/ int size;
    private Node first;

    //@ ensures \result.size == 0;
    public LinkedList () 
    {
        size = 0;
        first = null;
    }

    public void add(int index, Element element) {
        Node newNode = new Node(element);
        if (index == 0) {
            newNode.next = first;
            first = newNode;
        } else {
            Node p = getNode(index-1);
            newNode.next = p.next;
            p.next = newNode;
        }
        size = size + 1;
    }

    //@ ensures this.size == \old(size) - 1;
    public void remove(Element element) 
    {
    	if (first==null||element==first.getElement()||this.contain(element)==false)	
        	//if this is an empty list
    		//if the element that want to be removed is the first element
        	//if this element is not in the list
    	{    		
			size=0;
		}
    	else 
    	{
    		findBefore(element).next=findBefore(element).next.next;
    		size=size-1;
    	}
    }

    /**4.18
     * first version of the find method:
     * returns the Node immediately before the first occurrance of the specified Element
     * if the specified Element is first on the list, or is not contained on the list, 
     * the method returns null*/
    public boolean contain (Element element)
    {
        Node p = first;
        while (p.next!=null) 
        {    
            if (p.getElement()==element)
            {
            	return true;
            }
            else 
            {
                p = p.next;
            }
        }
        return false;
    }
    public Node findBefore(Element element) 
    {
    	
    	if (first==null||element==first.getElement()||this.contain(element)==false)
    	{
    		return null;
    	}
    	else 
   		/**Walk through the list from the beginning until you meet a node whose next link points you your current node.*/
    	{
            Node p = first;
            while (p.next.getElement()!=element) 
            {
                p = p.next;
            }
            return p;
    	}
    }

    //@ requires 0 <= index && index < this.size();
    public Element get(int index) {
        Node p = getNode(index);
        return p.element;
    }

    //@ requires 0 <= i && i < this.size();
    private /*@ pure @*/ Node getNode(int i) {
        Node p = first;
        int pos = 0;
        while (pos != i) {
            p = p.next;
            pos = pos + 1;
        }
        return p;
    }

    //@ ensures \result >= 0;
    public /*@ pure @*/ int size() {
        return size;
    }

    public class Node {
        private Element element;
        public Node next;

        public Node(Element element) {
            this.element = element;
            this.next = null;
        }

        public Element getElement() {
            return element;
        }
    }
}
