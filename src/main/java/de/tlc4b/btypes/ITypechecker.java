package de.tlc4b.btypes;

import de.be4.classicalb.core.parser.node.Node;


public interface ITypechecker {
	public void setType(Node node, BType type);
	public void updateType(Node node, AbstractHasFollowers oldType, BType newType);
}
