package controller;

/**
 * Exception for indexes outside the board.
 * @author Corjan van den Brink
 * @version 2019.01.24
 */
@SuppressWarnings("serial")
public class InvalidIndexException extends Exception {

	int index;

	public InvalidIndexException(int index) {
		this.index = index;
	}

	public String getMessage() {
		return "Index is out of bounds." + "(" + index + ")" + "is invalid";
	}

}
