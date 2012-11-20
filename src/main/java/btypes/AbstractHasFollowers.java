package btypes;


import java.util.ArrayList;

import de.be4.classicalb.core.parser.node.Node;

public abstract class AbstractHasFollowers implements BType{

	public ArrayList<Object> followers = new ArrayList<Object>();

	public void addFollower(Object obj){
		if(!followers.contains(obj)){
			followers.add(obj);
		}
		
	}
	
	public String printFollower(){
		String res = "[";
		for (Object o : followers) {
			res+= o;
			res+= o.hashCode();
			if(o instanceof Node)
				res+= ((Node) o).getStartPos();
			res += ", ";
		}
		res+= "]";
		return res;
	}
	
	public void deleteFollower(Object obj){
		followers.remove(obj);
	}
	
	
	
	public void setFollowersTo(BType newType, ITypechecker typechecker){
		for (Object obj: followers) {
			if(obj instanceof Node){
				typechecker.setType((Node) obj, newType);
			}else if(obj instanceof SetType){
				((SetType) obj).setSubtype(newType);
			}else if(obj instanceof IntegerOrSetOfPairType){
				((IntegerOrSetOfPairType) obj).update(this, newType, typechecker);
			}else if(obj instanceof PairType){
				((PairType) obj).update(this, newType);
			}else if(obj instanceof SequenceType){
				((SequenceType) obj).setSubtype(newType);
			}
			else{
				throw new RuntimeException("Missing follower type: "+ obj.getClass());
			}
		}
	}
}
