module ABZCaseStudy_ComputePlan

/* 
File-------------------+ ABZCaseStudy_ComputePlan_CS4710.als
Course--------------+ Model Driven Software Development (Michigan Tech CS4710)
Author(s)-----------+ Seamus Barry, John Bowie, Conner Born, Caden Rose
Semester-----------+ Fall 2025
Date Created------+ 10/29/2025
Description---------+This Alloy module aims to model the ComputePlan modules of the ABZ 2026 Case Study: "A Planetary Rover".
-------------------------The Rover's mission is to visit each of the 'Goal's without running into an obsticle or running out of charge. A path of
-------------------------x,y coordinates is the output of the path calculation. If the Rover calculates paths with the same cost, the path that 
-------------------------leaves the Rover with the most amount of charge will be selected.
-------------------------see https://github.com/trarse-nii/ABZ2026-case-study/blob/main/doc/document_v1.pdf for more information
*/

open util/ordering[XCoord] // orders the x-coordinates
open util/ordering[YCoord] // orders the y-coordinates
open util/ordering[ChargeLevel] // orders the charge levels

// pseudo integers
enum XCoord {x0, x1, x2, x3, x4, x5, x6, x7, x8, x9, x10} // can expand later
enum YCoord {y0, y1, y2, y3, y4, y5, y6, y7, y8, y9, y10} // can expand later 
enum ChargeLevel {c0, c1, c2, c3, c4, c5, c6, c7, c8, c9, c10} // can expand later


// -------------- Signatures  -------------- //


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
	charge: one ChargeLevel,	// The current charge
	currentPath: one Path		// The current path
}


// ----------------- Facts  ------------------//


fact {
	// Initialize the rover
	InitRover 

	// Select the Map
	MapTwo

	// Initialze the currentPath to only be the starting position
	Rover.currentPath.positions = Path.start

	 // Every path has a valid structure
	always ValidPathStructure[Path]

	// The map never changes
	always StaticMap 
}


// -------------- Predacates --------------//

/* Initializes the Rover */
pred InitRover {
	// Rover starts at position (x0, y0) with charge c10
	some r: Rover, pos: Position | {
		pos.x = x0
		pos.y = y0
		r.currentPos = pos
		r.charge = c10
	}
}

/* Is the path structure valid? */
pred ValidPathStructure[p: Path] {
	// The start point ahs no previous positon
	no p.start.~(p.nextPos)

	// The end point has no next position
	no p.end.(p.nextPos)

	// All positions that are not the end position have one next position
	all pos: (p.positions - p.end) | one pos.(p.nextPos)

	// All positions are reachable from the starting position
	p.positions = p.start.*(p.nextPos)
}

/* Does the Map stay unchanged? */
pred StaticMap {
	Obstacle' = Obstacle
	Charger' = Charger
	Goal' = Goal
}


// ------------------ Maps -----------------//


/* 
	Expected Path: (x0, y0), (x0, y1), (x0, y2), (y2, x1), (x2, y2)
	Note* map only looks visually appealing in the Alloy text editor

	y2     + - - - - - - - - - - - ->Goal
		 |
		 |
	y1	 |	   Obstacle
		 |
		 |
	y0  Start	   Obstacle
		x0		x1		x2
 */
pred MapOne {some o1: Obstacle, o2: Obstacle - o1,  g: Goal, c: Charger | MapOne[o, g, c]}
pred MapOne[o1: Obstacle, o2: Obstacle, g: Goal, c: Charger] {
	// Obstacles
	o1.x = x1 and o1.y = y1
	o2.x = x1 and o2.y = y0

	// Goals
	g.x = x2 and g.y = y2

	// Chargers
	c.x = x0 and c.y = y2
}

/* 
	Expected Path: (x0, y0), (x0, y1), (x0, y2), (x0, y3), (x0, y4), (x1, y4), (x2, y4), (x2, y3), (x2, y2), (x3, y2), (x4, y2), (x4, y3), (x4, y4)
	Note* map only looks visually appealing in the Alloy text editor

	y4  Goal - - - - - - - - - - - - +			     Goal
		 |				  |				 ^
		 |				  |				 |
	y3	 |          Obstacle        |        Obstacle        |
		 |				  |				 |
		 |				  |				 |
	y2     |			     Charge - - - - - - - - - - +
		 |
		 |
	y1	 |
		 |
		 |
	y0  Start	   
		x0		x1		x2		x3		x4
 */
pred MapTwo {some o1: Obstacle, o2: Obstacle - o1, o3: Obstacle - (o1+o2), g1: Goal, g2: Goal - g1, c: Charger | MapTwo[o1, o2, o3, g1, g2, c]}
pred MapTwo [o1: Obstacle, o2: Obstacle, o3: Obstacle, g1: Goal, g2: Goal, c: Charger] {
	// Obstacles
	o1.x = x3 and o1.y = y3
	o2.x = x3 and o2.y = y4
	o3.x = x1 and o3.y = y3
	
	// Goals
	g1.x = x0 and g1.y = y4
	g2.x = x4 and g2.y = y4

	// Chargers
	c.x = x2 and c.y = y2

	no m: MapObject | m != o1 and m != o2 and m != o3 and m != g1 and m != g2 and m != c
}


// -------------- Functions --------------//


// Returns the x coordinate of the map object
fun x[m: MapObject]: one XCoord {
	m.location.x
}


// Returns the y coordinate of the map object
fun y[m: MapObject]: one YCoord {
	m.location.y
}

pred show {}
run show for 10


