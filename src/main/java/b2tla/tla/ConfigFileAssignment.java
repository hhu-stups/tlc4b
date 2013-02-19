package b2tla.tla;

import de.be4.classicalb.core.parser.node.Node;

public class ConfigFileAssignment {
	private final Node left;
	private final Node right;

	public ConfigFileAssignment(Node left, Node right) {
		this.left = left;
		this.right = right;
	}

	public Node getLeft() {
		return left;
	}

	public Node getRight() {
		return right;
	}
	
	

}
