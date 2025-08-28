package de.tlc4b.tlc;

import de.tlc4b.TLC4BGlobals;
import tlc2.output.Message;

import java.util.*;

public abstract class TLCMessageListener extends Thread {

	private volatile boolean tlcRunning = true;
	private final List<Message> messages = new ArrayList<>();
	private int lastMessageIndex = 0;

	public TLCMessageListener() {
		super("TLCMessageListener");
		this.setDaemon(true);
	}

	@Override
	public final void run() {
		while (this.tlcRunning) {
			List<Message> currentMessages = TLC4BGlobals.getCurrentMessages();
			int currentMessageIndex = currentMessages.size();
			if (this.lastMessageIndex < currentMessageIndex) {
				for (int i = this.lastMessageIndex; i < currentMessageIndex; i++) {
					this.messages.add(currentMessages.get(i));
					onMessage(currentMessages.get(i));
				}
				this.lastMessageIndex = currentMessageIndex;
			}
		}
	}

	public final void finish() {
		this.tlcRunning = false;
		this.interrupt();
	}

	protected abstract void onMessage(Message message);

	public final List<Message> getMessages() {
		return this.messages;
	}
}
