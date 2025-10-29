module ABZCaseStudy_ComputePlan

open util/ordering[XCoord] // orders the x-coordinates
open util/ordering[YCoord] // orders the y-coordinates
open util/ordering[ChargeLevel] // orders the charge levels

// pseudo integers
enum XCoord {x0, x1, x2, x3} // can expand later
enum YCoord {y0, y1, y2, y3} // can expand later 
enum ChargeLevel {c0, c1, c2, c3, c4, c5, c6, c7, c8, c9, c10} // can expand later

// -------------- Signatures  --------------//

// 2D position
sig Position {
	x: one XCoord,	// The x-coordinate
	y: one YCoord		// The y-coordinate
}

// Objects on the Map that have a position
sig MapObject {
	location: one Position	// The objects location
}

sig Goal extends MapObject {}		// The Goal Objects
sig Charger extends MapObject {}	// The Charger Objects
sig Obstacle extends MapObject {}       // The Obstacle Objects

// The calculated Path to reach all Goals without running out of Charge
sig Path {
	positions: set Position,				// The set of positions in the path
	start: one Position,					// The initial position
	end: one Position,					// The terminal position
	nextPos: positions -> lone positions	// The order of positions
}

// The current state of the Rover
sig Rover {
	currentPos: one Position,	// The current x,y position
	charge: one ChargeLevel	// The current charge
}
