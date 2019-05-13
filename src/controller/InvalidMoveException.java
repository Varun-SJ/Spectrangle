package controller;

import model.MoveType;

/**
 * Exception for constructing moves using the wrong constructor.
 * @author Corjan van den Brink
 * @version 2019.01.24
 */
@SuppressWarnings("serial")
public class InvalidMoveException extends Exception {
	MoveType type;
	
	public InvalidMoveException(MoveType type) {
		this.type = type;
	}

	public String getMessage() {
		return "This Move constructor requires a different MoveType than " + type.toString();
	}

}
