//SIGNATURES
abstract sig User{
username: one String,
email: one String,
Password: one String
}

enum Boolean{
True, False
}

sig Position {
xCoord: one Int,
yCoord: one Int
}	

sig Passenger extends User{
request: lone Request,
reserve: set Reservation,
joins: lone SharedRide
}

sig TaxiDriver extends User{
taxiId: one Int,
availability: one Boolean,
belongsTo: one Queue,
AcceptOrRefuse: lone Request
}

sig Request {
creator: one Passenger,
creates: one Request,
acceptedOrRefusedBy: one TaxiDriver
}

sig Reservation extends Request{
reserver: Passenger,
Shared: one Boolean,
createsShared: one SharedRide
}

sig Ride{
destination: one Position,
createdBy: one Request,
handledBy: one TaxiDriver
}

sig ReservedRide extends Ride{
StartingPosition: one Position,
lenght: one Int,
reservedBy: one Reservation
}

sig SharedRide extends ReservedRide{
joinedBy: set Passenger
}

sig Queue {
has: set TaxiDriver
}


//FACTS

fact noTwoUsernameEquals{
	no disj u1,u2: User | u1.username = u2.username
}

fact noTwoUserWithSameRequest{
	no disj p1, p2: Passenger | p1.request = p2.request
}

fact noTwoUserWithSameReservation{
	no disj p1, p2: Passenger | all r: Reservation | r in p1.reserve implies r not in p2.reserve
}

fact NotAvailableTaxiNotInQueue {
	all td: TaxiDriver | all q: Queue | td.availability = False implies td.belongsTo not in q
}


//ASSERTIONS

assert OnlyOneRequestPerPassenger {
	all p: Passenger | #p.request = 1
}
check OnlyOneRequestPerPassenger for 5

assert noRequestIfIncomingTaxi{
	all p: Passenger, r: Ride | p in r.createdBy.creator implies UserRequests[p, p.request] = False
}
check noRequestIfIncomingTaxi for 5

assert TaxiInQueueOnlyIfAvailable {
	all t: TaxiDriver, q: Queue | t in q.has <=> t.availability = True
	all t: TaxiDriver, q: Queue | t.belongsTo = q <=> t.availability = True
}
check TaxiInQueueOnlyIfAvailable for 5

assert StartingPosAndDestinationNotEquals {
	all rr: ReservedRide | rr.StartingPosition != rr.destination
}
check StartingPosAndDestinationNotEquals for 5

//assert that a passenger can't join a shared ride created by him
assert 	PassengerJoin{
	all sr: SharedRide | sr.createdBy.reserver not in sr.joinedBy
}
check PassengerJoin for 5


//PREDICATES

pred show(){
all p: Passenger | 
#p.request>1
}
run show for 5

pred UserRequest {
	all p1, p2: Passenger, r: Request | r not in p1.request implies 	p2.request = p1.request + r
}
run UserRequest for 5

pred JoinUserToSharedRide {
	all p: Passenger, sr, sr': SharedRide | p not in sr.joinedBy implies sr'.joinedBy = sr.joinedBy + p
}
run JoinUserToSharedRide for 5



//FUNCTIONS

fun UserRequests[p: Passenger, r: Request]: one Boolean {
	#p.request=0 implies True else False
}
