package communication;

/**
 * Centralized protocol definition to implement in the Client, ClientHandler and Server.
 * @author Corjan van den Brink
 * @version 2019.01.30
 */
public interface Protocol {
	// Client side
	public static final String SERVERFEATURES = "server_features";
	public static final String PLACE = "place";
	public static final String DISCARD = "discard";
	public static final String PASS = "pass";
	
	// Server side
	public static final String CLIENTFEATURES = "client_features";
	public static final String PLAY = "play";
	public static final String WAITING = "waiting";
	public static final String ENTERED = "entered";
	public static final String START = "start";
	public static final String DISCONNECTED = "disconnected";
	public static final String END = "end";
	public static final String YOURTURN =  "yourturn";
	public static final String PLACEUPDATE = "place_update";
	public static final String TILESUPDATE = "tiles_update";
	
	// Errors
	public static final String ERROR = "error";
	public static final String ERRORERROR = "error 0 error";
	public static final String USERNAMETAKEN = "error 1 username is taken";
	public static final String INVALIDMOVE = "error 2 invalid move";
	public static final String NOTYOURTURN = "error 3 not your turn";
	public static final String UNKNOWNCOMMAND = "error 4 unknown command";
	public static final String INVALIDCOMMAND = "error 5 invalid command";
	public static final String INVALIDPARAMETERS = "error 6 invalid parameters";
}
