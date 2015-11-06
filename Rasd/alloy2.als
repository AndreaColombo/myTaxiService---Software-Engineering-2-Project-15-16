//SIGNATURES

abstract sig Ride{
start: one Position,
driver: one TaxiDriver
}

sig InstantRide extends Ride{
requestedBy: one Passenger,
}

sig ReservedRide extends Ride{
reservedBy: one Passenger,
destination: one Position,
Time: one Int
}

sig SharedRide extends ReservedRide  {
joinedBy: set Passenger,
itinerary: set Position
}

sig Position{
}

sig Passenger{
}

sig TaxiDriver{
}


//FACTS

fact NoNegativeTime{
all rr: ReservedRide | rr.Time >=0
}

fact NoNullPassenger{
all r: InstantRide | #r.requestedBy > 0
all rr: ReservedRide | #rr.reservedBy > 0
all sr: SharedRide | #sr.joinedBy>=0
}

fact NoReservationInLessThan30Minutes{

no disj rr1, rr2: ReservedRide | (rr1.reservedBy = rr2.reservedBy and !(rr1.Time-rr2.Time < 30 and rr2.Time-rr1.Time < 30))
}

fact OnlyOneRidePerTaxi {
all td: TaxiDriver | all disj r1, r2: Ride | assignRide [r1, td] implies (td in r1.driver implies td not in r2.driver) 
}

fact StartingPositionAndDestinationNotEquals{
//Starting position and destination not the same
all rr: ReservedRide | !(rr.start=rr.destination)
}

fact JoinAndReservation{
//If a passenger reserves a ride he can't join it
all p: Passenger | all disj sr1,sr2:SharedRide | joinRide[p, sr1,sr2] implies (p in sr1.joinedBy <=> p not in sr1.reservedBy)
}


//ASSERTIONS

assert NoMoreThanOneDriver {
all disj td1, td2: TaxiDriver | all r: Ride | (r.driver = td1 implies r.driver != td2) and (r.driver = td2 implies r.driver != td1)
}
check NoMoreThanOneDriver for 5	

//Check that there can't be two rides created by the same user that have departure time closer that 30 minutes
assert NoTooCloseRide{
all disj rr1, rr2: ReservedRide | rr1.reservedBy = rr2.reservedBy implies (rr1.Time-rr2.Time > 30 or rr2.Time-rr1.Time > 30)
}
check NoTooCloseRide for 5


//PREDICATES

//show all
pred show(){
#InstantRide>1
#ReservedRide>1
#SharedRide>1
#Passenger>1
#TaxiDriver>1
#Position>1 }
run show for 5

//show share rides
pred showShared(){
#ReservedRide > 1
#SharedRide = 2
#Passenger = 3
#TaxiDriver = 2
#InstantRide = 0
#reservedBy > 1
#Position = 2
}
run showShared for 5

//show rides
pred showRides(){
#ReservedRide >1
#InstantRide >1
#SharedRide > 1}
run showRides for 5

//Pred to assing a ride to a taxi driver
pred assignRide (r: Ride, td: TaxiDriver){r.driver = td}
run assignRide for 5

pred joinRide(p:Passenger, sr1, sr2: SharedRide){sr1.joinedBy = sr1.joinedBy+p}
run joinRide for 5
