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
enum YCoord {y0, y1, y2, y3, y4, y5, y6, y7, y8, y9, y10}         // can expand later 
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
sig Charger extends MapObject {}  	// The Charger Objects
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
	var currentPos: one Position,		// The current x,y position
	var charge: one ChargeLevel,	// The current charge
	var currentPath: one Path		// The current path
}

// A map object the rover can traverse
sig Map {
	obstacles: set Obstacle,	// The set of obstacles
	chargers: set Charger,	// The set of chargers
	goals: set Goal,		// The set of goals
	topEdge: one YCoord,   // The maximum traversable y value
	rightEdge: one XCoord   // The maximum traversable x value
}
one sig ActiveMap extends Map {} // The Map the Rover is activly traversing


// ----------------- Facts  ------------------//


fact {
	 // Every path has a valid structure
	always ValidPathStructure

	// There are never any extra map objects other than the ones defined by each map
	always no m: MapObject | m not in ActiveMap.(obstacles + goals + chargers)

	// The active map is the only map
	always Map = ActiveMap
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
		r.currentPath.start = pos
		r.currentPath.end = pos
	}

	// There is only ever 1 rover
	always #Rover = 1
}

/* Is the path structure valid? */
pred ValidPathStructure {all p: Path | ValidPathStructure[p]}
pred ValidPathStructure[p: Path] {
	// The start point has no previous positon
	no p.start.~(p.nextPos)

	// The end point has no next position
	no p.end.(p.nextPos)

	// All positions that are not the end position have one next position
	all pos: (p.positions - p.end) | one pos.(p.nextPos)

	// All positions that are not the start position have a prev position
	all pos: (p.positions - p.start) | one pos.~(p.nextPos)

	// All positions are reachable from the starting position
	p.positions = p.start.*(p.nextPos)

	// There are never any obstacles inside of a Rover's current path
	no (ActiveMap.obstacles.location & Rover.currentPath.positions)

	// There is only ever one path, the current path
	Path = Rover.currentPath
}

/* Does Rover r lower its charge at this time? */
pred lowerCharge[r: Rover] {
	// Pre-conditions
	r.charge != c0 // r must have some charge

	// Post-conditions
	r.charge' = prev[r.charge]
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
pred SelectMapOne {some o1: Obstacle, o2: Obstacle - o1,  g: Goal, c: Charger | SelectMapOne[o1, o2, g, c]}
pred SelectMapOne[o1: Obstacle, o2: Obstacle, g: Goal, c: Charger] {
	// Set Map Boundary
	ActiveMap.rightEdge = x2
	ActiveMap.topEdge = y2

	// Obstacles
	o1.x = x1 and o1.y = y1
	o2.x = x1 and o2.y = y0
	ActiveMap.obstacles = o1 + o2

	// Goals
	g.x = x2 and g.y = y2
	ActiveMap.goals = g

	// Chargers
	c.x = x0 and c.y = y2
	ActiveMap.chargers = c
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
pred SelectMapTwo {some o1: Obstacle, o2: Obstacle - o1, o3: Obstacle - (o1+o2), g1: Goal, g2: Goal - g1, c: Charger | SelectMapTwo[o1, o2, o3, g1, g2, c]}
pred SelectMapTwo [o1: Obstacle, o2: Obstacle, o3: Obstacle, g1: Goal, g2: Goal, c: Charger] {
	// Set Map Boundary
	ActiveMap.rightEdge = x4
	ActiveMap.topEdge = y4

	// Obstacles
	o1.x = x3 and o1.y = y3
	o2.x = x3 and o2.y = y4
	o3.x = x1 and o3.y = y3
	ActiveMap.obstacles = o1 + o2 + o3
	
	// Goals
	g1.x = x0 and g1.y = y4
	g2.x = x4 and g2.y = y4
	ActiveMap.goals = g1 + g2

	// Chargers
	c.x = x2 and c.y = y2
	ActiveMap.chargers = c
}

/*

// ------- Single Step Traversals ------//

pred TraverseUp {some r: Rover | TraverseUp[r] }
pred TraverseUp [r: Rover] {
	// Pre-conditions
	r.currentPos.y in prevs[prev[ActiveMap.topEdge]] // r's current position is < maximum traversable y value
	
	// Post-conditions (changed)
	r.currentPos'.y = next[r.currentPos.y]
	lowerCharge[r]

	// Post-conditions (un-changed)
	r.currentPos'.x = r.currentPos.x
	currentPath' = currentPath
}

pred TraverseRight {some r: Rover | TraverseRight[r] }
pred TraverseRight [r: Rover] {
	// Pre-conditions
	r.currentPos.x in prevs[prev[ActiveMap.rightEdge]] // r's current position is < maximum traversable x value
	
	// Post-conditions (changed)
	r.currentPos'.x= next[r.currentPos.x]
	lowerCharge[r]

	// Post-conditions (un-changed)
	r.currentPos'.y = r.currentPos.y
	currentPath' = currentPath
}

pred TraverseDown {some r: Rover | TraverseDown[r] }
pred TraverseDown [r: Rover] {
	// Pre-conditions
	r.currentPos.y != y0 // r's current position is > minimum traversable y value
	
	// Post-conditions (changed)
	r.currentPos'.y = prev[r.currentPos.y]
	lowerCharge[r]

	// Post-conditions (un-changed)
	r.currentPos'.x = r.currentPos.x
	currentPath' = currentPath
}

pred TraverseLeft {some r: Rover | TraverseLeft[r] }
pred TraverseLeft [r: Rover] {
	// Pre-conditions
	r.currentPos.x != x0 // r's current position is > minimum traversable y value
	
	// Post-conditions (changed)
	r.currentPos'.x = prev[r.currentPos.x]
	lowerCharge[r]

	// Post-conditions (un-changed)
	r.currentPos'.y = r.currentPos.y
	currentPath' = currentPath
}
*/

/* Traverses Rover r along is current path */
pred TraverseCurrentPath {some r: Rover | TraverseCurrentPath[r]}
pred TraverseCurrentPath [r: Rover] {
	// Pre-conditions
	r.currentPos = r.currentPath.start // r must be at the start of the path
	r.currentPath.start != r.currentPath.end // the path must be require at least one step

	
}

/* Updates Rover r's current path to the shortest path to reach all of its goals without running out of charge */
pred ComputePlan {some r: Rover | ComputePlan[r]}
pred ComputePlan [r: Rover] {
	
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

pred show {
	// Step 1: Initialize Rover and the Map
		InitRover and SelectMapTwo and

	// Step 2: Calcuate Current Path
		after (eventually (ComputePlan and

	// Step 3: Traverse Current Path
		after (eventually TraverseCurrentPath)))
}
run show for 3


