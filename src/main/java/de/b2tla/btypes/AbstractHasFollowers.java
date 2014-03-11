package de.b2tla.btypes;


import java.util.ArrayList;

import de.be4.classicalb.core.parser.node.Node;

public abstract class AbstractHasFollowers implements BType{

	public abstract boolean contains(BType other);
	
	public ArrayList<Object> followers = new ArrayList<Object>();

	public void addFollower(Object obj){
		if(!followers.contains(obj))
			followers.add(obj);
	}
	
	public String printFollower(){
		String res = "[";
		for (Object o : followers) {
			if(!(o instanceof Node)){
				res+= o.hashCode();
				res+= o.getClass();
				//IntegerOrSetOfPairType i = (IntegerOrSetOfPairType) o;
				res += " ";
			}
			
			
		}
		res+= "]";
		return res;
	}
	
	public void deleteFollower(Object obj){
		followers.remove(obj);
	}
	
	
	
	public void setFollowersTo(BType newType, ITypechecker typechecker){
		if (this == newType){
			return;
		}
		ArrayList<Object> list	= new ArrayList<Object>(followers);	
		for (Object obj: list) {
			if(obj instanceof Node){
				typechecker.setType((Node) obj, newType);
			}else if(obj instanceof SetType){
				((SetType) obj).setSubtype(newType);
			}else if(obj instanceof IntegerOrSetOfPairType){
				//System.out.println("this " +this + " old " + obj + "  new " + newType);
				((IntegerOrSetOfPairType) obj).update(this, newType, typechecker);
			}else if(obj instanceof PairType){
				((PairType) obj).update(this, newType);
			}else if(obj instanceof FunctionType){
				((FunctionType) obj).update(this, newType);
			}else if(obj instanceof StructType){
				((StructType) obj).update(this, newType);
			}
			else{
				throw new RuntimeException("Missing follower type: "+ obj.getClass());
			}
		}
		this.followers.clear();
		
	}
}
