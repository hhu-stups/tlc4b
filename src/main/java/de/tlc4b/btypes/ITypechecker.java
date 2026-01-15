package de.tlc4b.btypes;

import de.be4.classicalb.core.parser.node.Node;

public interface ITypechecker {
	void setType(Node node, BType type);
	void updateType(Node node, AbstractHasFollowers oldType, BType newType);
}
