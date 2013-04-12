package de.b2tla.tlc;

import java.util.HashMap;
import java.util.regex.Matcher;
import java.util.regex.Pattern;

import de.b2tla.util.StopWatch;

import tla2sany.drivers.SANY;
import tla2sany.modanalyzer.SpecObj;
import tla2sany.semantic.ModuleNode;
import tla2sany.semantic.OpDefNode;
import util.ToolIO;

public class ModuleMatcher {
	private final String fileName;
	private final HashMap<Integer, String> lineToNameMap;

	public ModuleMatcher(String fileName, String path) {
		this.fileName = fileName;
		this.lineToNameMap = new HashMap<Integer, String>();
		ModuleNode moduleNode = parse(fileName, path);
		evalActions(moduleNode);
	}

	public String getName(String string){
		int line = getLine(string);
		if(line == -1){
			return "Init";
		}
		String res = lineToNameMap.get(line);
		return res;
	}
	
	private void evalActions(ModuleNode moduleNode) {
		OpDefNode[] opdefs = moduleNode.getOpDefs();
		for (int i = 0; i < opdefs.length; i++) {
			OpDefNode opdef = opdefs[i];
			
			String module = opdef.getSource()
					.getOriginallyDefinedInModuleNode().getName().toString();
			if (module.equalsIgnoreCase(fileName)) {
				String opdefName = opdef.getName().toString();
				lineToNameMap.put(opdef.getLocation().beginLine(), opdefName);
			}
		}
	}

	private int getLine(String s){
		Pattern pattern = Pattern.compile("(line\\s)(\\d+)");
		Matcher matcher = pattern.matcher(s);
		boolean res = matcher.find();
		if(res){
			return Integer.parseInt(matcher.group(2));
		}else{
			return -1;
		}
	}
	
	private ModuleNode parse(String fileName, String path) {
		ToolIO.reset();
		ToolIO.setUserDir(path);
		SpecObj spec = new SpecObj(fileName, null);
		try {
			SANY.frontEndMain(spec, fileName, ToolIO.out);
		} catch (tla2sany.drivers.FrontEndException e) {
			System.out.println(e.getMessage());
			e.printStackTrace();
		}

		// RootModule
		ModuleNode n = spec.getExternalModuleTable().rootModule;
		if (spec.getInitErrors().isFailure()) {
			System.err.println(spec.getInitErrors());
			return null;
		}

		if (n == null) { // Parse Error
			System.out.println("hier");
			// System.out.println("Rootmodule null");
			System.out.println(allMessagesToString(ToolIO.getAllMessages()));
		}
		return n;
	}

	public static String allMessagesToString(String[] allMessages) {
		StringBuilder sb = new StringBuilder();
		for (int i = 0; i < allMessages.length - 1; i++) {
			sb.append(allMessages[i] + "\n");
		}
		return sb.toString();
	}
}
