package main

//----------------------------------------------
// Imports
//----------------------------------------------
import (
    "encoding/csv"
    "fmt"
    "log"
    "os"
    "strconv"
    "net"
    "io"
    "io/ioutil"
    "math"
    "bytes"
    "encoding/gob"
    "time"
    "reflect"
    "sync"
)
//----------------------------------------------

//----------------------------------------------
// Config
//----------------------------------------------
var data_Input = "./topologies/" //where we are reading topologies from (specify directory where each item is a topology)
var ip = "localhost" //what port we want to work on
var port = 6969 //what port number we want to start on (port increments by 1)
//"GF", "mGF", "FILO_GPGF", "ALL_GPGF", "G_FILO_GPGF", "G_ALL_GPGF"
//"FILO_GPmGF", "ALL_GPmGF", "G_FILO_GPmGF", "G_ALL_GPmGF"
var algorithms = []string{"GF", "mGF", "FILO_GPGF", "ALL_GPGF", "G_FILO_GPGF", "G_ALL_GPGF", "FILO_GPmGF", "ALL_GPmGF", "G_FILO_GPmGF", "G_ALL_GPmGF"} //all the algorithms we want to test
//var algorithms = []string{"mGF"}
var debug = false //true means extra print statements
var distance_Formula = "hyperbolic" //euclidean or hyperbolic
var buf_Size = 99999 //buffer size for reading
var output = "./results/out_9.csv"
//----------------------------------------------

//----------------------------------------------
// Globals
//----------------------------------------------
var curr_Algorithm string //the current algorithm we are using
var hops_Lock sync.Mutex //lock for processes
var hops int //the number of hops we have made
var process_Lock sync.Mutex //lock for processes
var open_Processes int //the number of open packets (not dropped or successed)
//----------------------------------------------

//----------------------------------------------
// Node Struct Declaration
//----------------------------------------------
type Node struct {
    IP		string	//the ip
    Port	int	//the port
    Number	int	//the node number
    Lat		float64 //latitude
    Long	float64 //longitude
    Theta	float64 //hyperbolic theta
    R		float64 //hyperbolic R
    Lock	sync.Mutex //lock for PIT
    Neighbors	[]int	//a list of all the neighbors nodes as numbers 
    Pit		[]PIT	//PIT needs to record incoming interface, outgoing interface, and name of the data
}
//----------------------------------------------

//----------------------------------------------
// PIT Struct Declaration
//----------------------------------------------
type PIT struct {
    Incoming    int	//the node number of the interface interface
    Outgoing	int	//the node number of the outgoing interface
    Name        string	//the name for the interest
}
//----------------------------------------------

//----------------------------------------------
// Packet Struct Declaration
//----------------------------------------------
type Packet struct {
    Previous	int	//the node number of the previous interface
    Destination	int	//the node number of the destination interface
    Interest_Data   int //0 if interest, 1 if data packet, 2 for shutdown signal
    Name	string	//the name for the interest
    Payload	string	//the payload if data
    //For gravity/pressure mode
    GP_Mode	int	//0 for gravity, 1 for pressure
    Nodes_Visit	[]int	//a list of the node numbers we have visited just in pressure node
    Num_Visit	[]int	//a list of the number of times we have visited a node just in pressure node
    GP_Distance float64 //the distance at local minimum
    //For metrics, do not count when adding
    Path_Traversed []int //records the path this packet has taken
    Pressure_Gauge int //counter for how many times this packet went it pressure mode
}
//----------------------------------------------

//----------------------------------------------
// Check Error Function
// Exits code if error
//----------------------------------------------
func check_Error(err error) {
	if err != nil {
		log.Fatal(err)
	}
}
//----------------------------------------------

//----------------------------------------------
// Hyperbolic distance function
// Returns the hyperbolic distance from A to B
// If the return value is NaN, return MaxFloat
//----------------------------------------------
func hyperbolic_Distance(A Node, B Node) float64{
	dtheta := math.Pi - math.Abs(math.Pi - math.Abs(A.Theta - B.Theta))
	if dtheta == 0{
		return math.Abs(A.R - B.R)
	}
	ret_Val := (math.Acosh(math.Cosh(A.R) * math.Cosh(B.R) - math.Sinh(A.R) * math.Sinh(B.R) * math.Cos(dtheta)))
	if math.IsNaN(ret_Val) == true{
		return math.MaxFloat64
	}
	return ret_Val
}
//----------------------------------------------

//----------------------------------------------
// Euclidean distance function
// Returns the euclidean distance from A to B
//----------------------------------------------
func euclidean_Distance(A Node, B Node) float64{
	ret_Val := (math.Pow((A.Lat-B.Lat),2) + math.Pow((A.Long-B.Long),2))
	if math.IsNaN(ret_Val) == true{
                return math.MaxFloat64
        }
        return ret_Val
}
//----------------------------------------------

//----------------------------------------------
// Distance Helper Function
//----------------------------------------------
func distance_Helper(A Node, B Node) float64{
	var distance float64
	if distance_Formula == "euclidean"{ //euclidean distance
		distance = euclidean_Distance(A, B)
	} else if distance_Formula == "hyperbolic"{ //hyperbolic distance
		distance = hyperbolic_Distance(A, B)
	} else{
		fmt.Println("Unrecognized distance formula! Exiting.")
		os.Exit(1)
	}
	return distance
}
//----------------------------------------------

//----------------------------------------------
// Dijkstra's, only counting number of hops
// Returns the optimal number of hops
//----------------------------------------------
func dijkstras(y int, z int, topology []*Node) int{
	local_hops := 0
	if y == z{ //if we are already done
		return local_hops
	}
	nodes := []int{y} //start with the current node
	for x := 0; x < len(topology); x++{ //maximum we go for each node in topology
		var new_Nodes []int
		for y := 0; y < len(nodes); y++{ //for each value
			new_Nodes = append(new_Nodes, find_Node(topology, nodes[y]).Neighbors...) //grab all its neighbors 
		}

		//Only look for unique nodes, as anything repeating will always be more hops 
		for y := 0; y < len(new_Nodes); y++{
			add_Node := true
			for z := 0; z < len(nodes); z++{
				if new_Nodes[y] == nodes[z]{
					add_Node = false
					break
				}
			}
			if add_Node == true{
				nodes = append(nodes, new_Nodes[y])
			}
		}
		local_hops++

		//if one of the values is at the destination
		for y := 0; y < len(nodes); y++{
                        if nodes[y] == z{
				return local_hops
			}
                }
	}
	return -1 //return -1 if fail to find
}
//----------------------------------------------

//----------------------------------------------
// GF Distance Helper
// Returns the neighbor with the closest distance to the end
//----------------------------------------------
func gf_Helper(curr_Node Node, end Node, neighbors []*Node) *Node{
	var distances []float64
        min_Distance := math.MaxFloat64
	//first check to see if a neighbor is the destination
	for x := 0; x < len(neighbors); x++{
		if neighbors[x].Number == end.Number{
			return neighbors[x]
		}
	}
        //calculate each distance, tracking the minimum
        for x := 0; x < len(neighbors); x++{
		distance := distance_Helper(end, *(neighbors[x]))
                debug_Print("\tNeighbor " + strconv.Itoa((*(neighbors[x])).Number) + ", distance " + fmt.Sprintf("%f", distance) + " \n")
                if distance < min_Distance{
                        min_Distance = distance
                }
                distances = append(distances, distance)
        }
        //return the node with the smallest distance
        index := -1
        for x := 0; x < len(neighbors); x++{
                if distances[x] == min_Distance{
                        index = x
                        break
                }
        }
	if index == -1{
                fmt.Println("Error finding node with smallest distance! Exiting.")
                os.Exit(1)
        }
        return neighbors[index]
}
//----------------------------------------------

//----------------------------------------------
// Encodes and sends a message
//----------------------------------------------
func send_Msg(packet Packet, c net.Conn) {
        var buf bytes.Buffer //where the encoded message is stored
	enc := gob.NewEncoder(&buf) //create an encoder
	err := enc.Encode(packet) //encode the current node and the destination node
	check_Error(err) //check for errors
	_, err = c.Write(buf.Bytes()) //send the destination over the connection
	check_Error(err) //check for errors
	err = c.Close() //close the connection
	check_Error(err) //check for errors
}
//----------------------------------------------

//----------------------------------------------
// Receives and decodes a message
// Returns the transmitted packet
//----------------------------------------------
func receive_Msg(c net.Conn) Packet{
	var packet Packet //the node we came from and the destination node number
	raw := make([]byte, buf_Size) //default buffer size of 
	_, err := c.Read(raw) //read the data into raw
	check_Error(err) //check for errors
	dec := gob.NewDecoder(bytes.NewBuffer(raw)) //creating a decoder
	err = dec.Decode(&packet) //decoding the value and storing it in args
	check_Error(err) //check for errors
	err = c.Close() //close the connection
	check_Error(err) //check for errors
	return packet
}
//----------------------------------------------

//----------------------------------------------
// Returns the LAST PIT entry corresponding to the named data we are looking for
// Returns dummy PIT with -2 if the PIT entry is not found
//----------------------------------------------
func index_PIT(curr_Node Node, name string) PIT{
        for x := len(curr_Node.Pit)-1; x >=0 ; x--{
		if curr_Node.Pit[x].Name == name{
			return curr_Node.Pit[x]
		}
	}
	return PIT{Incoming: -2, Outgoing: -2}
}
//----------------------------------------------

//----------------------------------------------
// Returns the LAST PIT entry corresponding to the named data we are looking for
// Must also match the outgoing interface (this function is used for return trips
// Returns dummy PIT with -2 if the PIT entry is not found
//----------------------------------------------
func index_PIT_Outgoing(curr_Node Node, name string, Outgoing int) PIT{
        for x := len(curr_Node.Pit)-1; x >=0 ; x--{
                if curr_Node.Pit[x].Name == name && curr_Node.Pit[x].Outgoing == Outgoing{
                        return curr_Node.Pit[x]
                }
        }
        return PIT{Incoming: -2, Outgoing: -2}
}
//----------------------------------------------

//----------------------------------------------
// Removes the last copy of local_PIT from the current nodes PIT
// If it cant find anything to remove, assume its already gone (race condition)
//----------------------------------------------
func remove_PIT(curr_Node *Node, local_PIT PIT) {
	for x := len((*curr_Node).Pit)-1; x >= 0; x--{ //find the index of the local_PIT inside all pit entries
		if (*curr_Node).Pit[x] == local_PIT{
			curr_Node.Pit = append((*curr_Node).Pit[:x], (*curr_Node).Pit[x+1:]...) //remove the PIT entry we just used
			break
		}
	}
}
//----------------------------------------------

//----------------------------------------------
//Returns the []*Node for each neighbor a node has
//----------------------------------------------
func find_Neighbors(topology []*Node, number int) []*Node{
        curr_node := find_Node(topology, number) //grad the current node
        var node_neighbors []*Node
        for y := 0; y < len(curr_node.Neighbors); y++{ //for each neighbor of the current node
                node_neighbors = append(node_neighbors, find_Node(topology, curr_node.Neighbors[y])) //based on the number, append the node
        }
        return node_neighbors
}
//----------------------------------------------

//----------------------------------------------
// Returns a node with the given value
// Returns a dummy node with -1 if that node doesnt exist
//----------------------------------------------
func find_Node(topology []*Node, number int) *Node{
        for x := 0; x < len(topology); x++{
                if (*topology[x]).Number == number{
                        return topology[x]
                }
        }
        return &Node{Number: -1} //return a dummy node if the node is not in the topology
}
//----------------------------------------------

//----------------------------------------------
// Returns the average a slice
//----------------------------------------------
func avg(arr []float64) float64{
        if len(arr) == 0{
                return 0.0
        }
        sum := 0.0
        for x := 0; x < len(arr); x++{
                sum = sum + arr[x]
        }
	return sum/float64(len(arr))
}
//----------------------------------------------

//----------------------------------------------
// Returns the std of a slice
//----------------------------------------------
func std(arr []float64) float64 {
	mean := avg(arr)
	std := 0.0
	for x := 0; x < len(arr); x++ {
		std = std + math.Pow(float64(arr[x])-mean, 2)
	}
	std = math.Sqrt(std/float64(len(arr)))
	return std
}
//----------------------------------------------

//----------------------------------------------
// Print statements in debug mode
//----------------------------------------------
func debug_Print(str string) {
        if debug == true{
                fmt.Printf(str)
        }
}
//----------------------------------------------

//----------------------------------------------
// Checks if we are following the reverse of the path 
// we took for successful packets for
// If reverse isn't taken, error and exit
//----------------------------------------------
func reverse_Check(path_Traversed []int) {
        for x := 0; x < len(path_Traversed); x++{
		if path_Traversed[x] != path_Traversed[len(path_Traversed)-1-x]{
			fmt.Printf("Error! Not following the reverse of the taken path!\n")
			for y := 0; y < len(path_Traversed); y++{
				if y == len(path_Traversed)-1{
					debug_Print(strconv.Itoa(path_Traversed[y]) + "\n")
				} else{
					debug_Print(strconv.Itoa(path_Traversed[y]) + ", ")
				}
			}
			os.Exit(1)
		}
	}
}
//----------------------------------------------

//----------------------------------------------
// Checks to make sure all PITs are empty on a packet success
// If PIT isnt clear, error and exit
//----------------------------------------------
func empty_PIT_Check(topology []*Node) {
	for x := 0; x < len(topology); x++{
		if len(topology[x].Pit) != 0{
			fmt.Printf("Error! PIT is not empty for node " + strconv.Itoa(topology[x].Number) + "!\n")
			for y := 0; y < len(topology[x].Pit); y++{
				debug_Print("IN: " + strconv.Itoa(topology[x].Pit[y].Incoming) + ", ")
				debug_Print("OUT: " + strconv.Itoa(topology[x].Pit[y].Outgoing) + "\n")
			}
			os.Exit(1)
		}
	}
}
//----------------------------------------------

//----------------------------------------------
// Calculates the size of a packet in bytes
//----------------------------------------------
func calc_Size(packet Packet) float64{
	size := 0.0
        v := reflect.ValueOf(packet)
	for i := 0; i < v.NumField(); i++{
		string_Type := v.Field(i).Kind().String()
		typeOfS := v.Type()
		if string_Type == "int"{
			if v.Field(i).Interface().(int) != -1{
				size = size + 4
			}
		} else if string_Type == "float64"{
			if v.Field(i).Interface().(float64) != -1.0{
				size = size + 8
			}
		} else if string_Type == "string"{
			if typeOfS.Field(i).Name == "Payload"{
				continue
			}
			size = size + float64(len(v.Field(i).Interface().(string)))
		} else if string_Type == "slice"{
			if typeOfS.Field(i).Name == "Path_Traversed"{
				continue
			}
			size = size + float64(len(v.Field(i).Interface().([]int))*4)
		} else{
			fmt.Printf("Error! Undefined type: " + string_Type + "\n")
			os.Exit(0)
		}
	}
	return size
}
//----------------------------------------------

//----------------------------------------------
// Calculates how many hops until we got to the destination
//----------------------------------------------
func dest_Hop(path []int, dest int) float64{
	counter := 0.0
	for x := 0; x < len(path); x++{
		if path[x] == dest{
			break
		}
		counter = counter + 1
	}
	return counter
}
//----------------------------------------------

//----------------------------------------------
// Server
//----------------------------------------------
func setup_Node(curr_Node *Node, shutdown_ACK chan int, packet_Contents chan Packet, topology []*Node) {
	l, err := net.Listen("tcp", curr_Node.IP+ ":" + strconv.Itoa(curr_Node.Port)) //listen on ip:port
	check_Error(err) //check for errors
	debug_Print("Node " + strconv.Itoa((*curr_Node).Number) + " up on " + (*curr_Node).IP + ":" + strconv.Itoa((*curr_Node).Port) + " \n")
	shutdown_ACK <- 1 //reuse this channel, send value when properly setup
	loop:
	for { //forever until blreak
		c, err := l.Accept() //accept a connection
		check_Error(err) //check for errors
		packet := receive_Msg(c) //receive and decode the message
		if packet.Previous == -999 && packet.Destination == -999 && packet.Interest_Data == 2 && packet.Name == "Shutdown"{
			break loop
		}
		go serviceConnection(curr_Node, shutdown_ACK, packet_Contents, topology, packet)
	}
        debug_Print("Shutting down Node " + strconv.Itoa(curr_Node.Number) + " \n")
        l.Close()
        shutdown_ACK <- 1
}
//----------------------------------------------

//----------------------------------------------
// Thread to handle connections
//----------------------------------------------
func serviceConnection(curr_Node *Node, shutdown_ACK chan int, packet_Contents chan Packet, topology []*Node, packet Packet){
	done := 0
	prev_Node := *find_Node(topology, packet.Previous) //the node we came from
	end := *find_Node(topology, packet.Destination) //the node we are going to
	debug_Print("Node " + strconv.Itoa((*curr_Node).Number) + " received a message from Node " + strconv.Itoa(prev_Node.Number) + " \n")
	next_Node := Node{Number: -9}
	var next_Nodes []Node
	local_PIT := index_PIT((*curr_Node), packet.Name)
	var goto_Jump = false

	//if the current node is the destination, we are going to start going backwards
	if (*curr_Node).Number == end.Number{
		debug_Print("Reached Destination\n")
		packet.Payload = "HelloWorld"
		packet.Interest_Data = 1
		if packet.GP_Mode == 1{
			packet.GP_Mode = 0
		}
		next_Node = *find_Node(topology, packet.Previous)//if the current previous node is undefined, use the previous number passed
		goto_Jump = true
	}

	//if we are completely done
	if local_PIT.Incoming == -1 && packet.Interest_Data == 1{
		curr_Node.Lock.Lock()
		remove_PIT(curr_Node, local_PIT)
		curr_Node.Lock.Unlock()
		debug_Print("Successful Packet\n")
		packet_Contents <- packet
	}else { //if we are not completely done
		if goto_Jump == true{
			goto SEND
		}
		if packet.Interest_Data == 1{ //if we are going back
			if curr_Algorithm == "FILO_GPGF" || curr_Algorithm == "G_FILO_GPGF" || curr_Algorithm == "FILO_GPmGF" || curr_Algorithm == "G_FILO_GPmGF"{ //these algorithms treat the PIT like a stack
				temp_Local_PIT := index_PIT_Outgoing((*curr_Node), packet.Name, packet.Previous)
				next_Node = *find_Node(topology, temp_Local_PIT.Incoming)
				remove_PIT(curr_Node, temp_Local_PIT)
			} else{ ////these algorithms forward to all entries in the PIT
				curr_Node.Lock.Lock()
				for{
					temp_Local_PIT := index_PIT((*curr_Node), packet.Name)
					if temp_Local_PIT.Incoming == -2{
						break
					}
					next_Nodes = append(next_Nodes, *find_Node(topology, temp_Local_PIT.Incoming))
					remove_PIT(curr_Node, temp_Local_PIT)
				}
				if len(curr_Node.Pit) != 0{ //assertion PIT is empty
					fmt.Printf("Error! Pit not empty for node: " + strconv.Itoa(curr_Node.Number) + "\n")
					os.Exit(1)
				}
				curr_Node.Lock.Unlock()
			}
		} else { //else, we need to find where to send the packet to, as we are not on the return trip (we can easily check this if there is a payload)
			//based on what algorithm we are doing, execute the helper function
			neighbors := find_Neighbors(topology, curr_Node.Number)
			drop_Packet := false
			if curr_Algorithm == "GF"{

				// Original Greedy Forwarding
				// The packet is forwarded to the neighbor that is closest to the destination. The packet is dropped if the chosen node is itself.
				// Returns the neighbor with the closest distance to the end, or a dummy node with -4 if we want to drop the packet

				//Call the helper
				next_Node = *(gf_Helper((*curr_Node), end, neighbors))

				//Packet drop condition
				if curr_Node.Number == next_Node.Number{ //drop packet if we send the packet to the current node
					drop_Packet = true
				}

			} else if curr_Algorithm == "mGF"{

				// Modified Greedy Forwarding
				// Same as GF, but the current node is excluded from the distance calculation, and the packet is dropped if passed to same neighbor
				// Returns the neighbor with the closest distance to the end, or a dummy node with -4 if we want to drop the packet

				//Remove the current node from the list of neighbors
				temp_Neighbors := neighbors
				for x := 0; x < len(neighbors); x++{
					if ((*(neighbors[x])).Number) == curr_Node.Number{
						temp_Neighbors = append(temp_Neighbors[:x], temp_Neighbors[x+1:]...)
						break
					}
				}

				//Call the helper
				next_Node = *(gf_Helper((*curr_Node), end, temp_Neighbors))

				//Packet drop condition
				for x := 0; x < len(curr_Node.Pit); x++{
					if curr_Node.Pit[x].Outgoing == next_Node.Number && curr_Node.Pit[x].Name == packet.Name{ //drop packet if we send the packet to the same node neighbor
						drop_Packet = true
						break
					}
				}

			} else if curr_Algorithm == "FILO_GPGF" || curr_Algorithm == "ALL_GPGF" || curr_Algorithm == "G_FILO_GPGF" || curr_Algorithm == "G_ALL_GPGF" || curr_Algorithm == "FILO_GPmGF" || curr_Algorithm == "ALL_GPmGF" || curr_Algorithm == "G_FILO_GPmGF" || curr_Algorithm == "G_ALL_GPmGF"{
				// Gravity-Pressure Greedy Forwarding
				// This algorithm works by having a packet initially start in gravity mode. 
				// If a local minimum is reached, calculate the distance to destination from local minimum, and enter pressure mode. 
				// In pressure mode, a packet tracks all nodes it has visited, and how many times it visited each node. 
				// When a node gets a packet, it sends it to the neighbor that node has visited the least with the lowest distance to its destination. 
				// This continues until the packet reaches the destination, or until the current distance is smaller than local minimum distance, 
				// in which case it then switches back to gravity mode. 

				if !(curr_Algorithm == "FILO_GPmGF" || curr_Algorithm == "ALL_GPmGF" || curr_Algorithm == "G_FILO_GPmGF" || curr_Algorithm == "G_ALL_GPmGF"){
					//Call the helper
					if packet.GP_Mode == 0{
						next_Node = *(gf_Helper((*curr_Node), end, neighbors))
						if curr_Node.Number == next_Node.Number{
							debug_Print("Entering Pressure Mode\n")
							//Calculate the distance to destination from local minimum (current node)
							packet.GP_Distance = distance_Helper(end, (*curr_Node)) //record the disance
							packet.GP_Mode = 1 //enter pressure mode
						}
					}
				} else{
					if packet.GP_Mode == 0{
						temp_Neighbors := neighbors
						for x := 0; x < len(neighbors); x++{
							if ((*(neighbors[x])).Number) == curr_Node.Number{
								temp_Neighbors = append(temp_Neighbors[:x], temp_Neighbors[x+1:]...)
								break
							}
						}

						//Call the helper
						next_Node = *(gf_Helper((*curr_Node), end, temp_Neighbors))

						//Packet drop condition
						for x := 0; x < len(curr_Node.Pit); x++{
							if curr_Node.Pit[x].Outgoing == next_Node.Number && curr_Node.Pit[x].Name == packet.Name{ //drop packet if we send the packet to the same node neighbor
								debug_Print("Entering Pressure Mode\n")
								//Calculate the distance to destination from local minimum (current node)
								packet.GP_Distance = distance_Helper(end, (*curr_Node)) //record the disance
								packet.GP_Mode = 1 //enter pressure mode
								break
							}
						}
					}
				}

				//if we are in pressure mode
				if packet.GP_Mode == 1{

					//Calculate how many times we have visited each neighbor
					var min_Distances_Num []int
					var min_Distances []int
					for x := 0; x < len(neighbors); x++{
						min_Distances_Num = append(min_Distances_Num, neighbors[x].Number)
						visit_Before := false
						for y := 0; y < len(packet.Nodes_Visit); y++{
							if neighbors[x].Number == packet.Nodes_Visit[y]{
								min_Distances = append(min_Distances, packet.Num_Visit[y])
								visit_Before = true
								break
							}
						}
						if visit_Before == false{
							min_Distances = append(min_Distances, 0)
						}
					}

					//Calculate the nodes we have visited the least
					var min []int
					min_Distance := math.MaxInt64
					for x := 0; x < len(min_Distances); x++{ //first pass to get the minimum
						if min_Distances[x] <= min_Distance{
							min_Distance = min_Distances[x]
						}
					}
					for x := 0; x < len(min_Distances); x++{ //second pass to get the indexs
						if min_Distances[x] == min_Distance{
							min = append(min, min_Distances_Num[x])
						}
					}

					//Keep only nodes from the list of minimum visits
					var new_Neighbors []*Node
					for x := 0; x < len(min); x++{
						new_Neighbors = append(new_Neighbors, find_Node(topology, min[x]))
					}
					next_Node = *(gf_Helper((*curr_Node), end, new_Neighbors)) //call the helper

					//Calculate the new distance 
					distance := distance_Helper(end, next_Node)

					//If the new distance is less, go back to gravity mode
					if distance < packet.GP_Distance{
						debug_Print("Leaving Pressure Mode\n")
						packet.GP_Mode = 0
					}

					if curr_Algorithm == "FILO_GPGF" || curr_Algorithm == "ALL_GPGF" || curr_Algorithm == "FILO_GPmGF" || curr_Algorithm == "ALL_GPmGF"{
						//Track all nodes it has visited
						//Track how many times it visited each node
						visit_Before := false
						for x := 0; x < len(packet.Nodes_Visit); x++{
							if packet.Nodes_Visit[x] == next_Node.Number{
								packet.Num_Visit[x] = packet.Num_Visit[x] + 1
								visit_Before = true
								break
							}
						}
						if visit_Before == false{
							packet.Nodes_Visit = append(packet.Nodes_Visit, next_Node.Number)
							packet.Num_Visit = append(packet.Num_Visit, 1)
						}
					}

					packet.Pressure_Gauge = packet.Pressure_Gauge + 1 //increment the pressure gauge
				}

				if curr_Algorithm == "G_FILO_GPGF" || curr_Algorithm == "G_ALL_GPGF" || curr_Algorithm == "G_FILO_GPmGF" || curr_Algorithm == "G_ALL_GPmGF"{
					//Globally track all nodes it has visited
                                        //Globally track how many times it visited each node
					visit_Before := false
					for x := 0; x < len(packet.Nodes_Visit); x++{
						if packet.Nodes_Visit[x] == next_Node.Number{
							packet.Num_Visit[x] = packet.Num_Visit[x] + 1
							visit_Before = true
							break
						}
					}
					if visit_Before == false{
						packet.Nodes_Visit = append(packet.Nodes_Visit, next_Node.Number)
						packet.Num_Visit = append(packet.Num_Visit, 1)
					}
				}

			} else{
				fmt.Println("Unrecognized algorithm! Exiting.")
				os.Exit(1)
			}
			if drop_Packet == true{ //signal to drop packet
				debug_Print("Dropped Packet\n")
				done = 1
				shutdown_ACK <- packet.Interest_Data
			} else{
				curr_Node.Lock.Lock()
				curr_Node.Pit = append((*curr_Node).Pit, PIT{packet.Previous, next_Node.Number, packet.Name}) //update the Pit if we did the algorithm
				curr_Node.Lock.Unlock()
			}
		}
		SEND:
		if done == 0{ //needs to be here incase we decide to drop a packet
			if len(next_Nodes) == 0 && next_Node.Number != -9{ //a single, declared next node
				next_Nodes = append(next_Nodes, next_Node)
			} else if len(next_Nodes) == 0 && next_Node.Number == -9{ //no next nodes
				debug_Print("Dropped Packet\n")
                                shutdown_ACK <- packet.Interest_Data
			} else{
				process_Lock.Lock()
				open_Processes = open_Processes + len(next_Nodes) - 1
				process_Lock.Unlock()
			}
			for 0 < len(next_Nodes){
				next_Node, next_Nodes = next_Nodes[0], next_Nodes[1:]
				if next_Node.Number == -1{
					debug_Print("Successful Packet\n")
					packet_Contents <- packet
					continue
				}
				c, err := net.Dial("tcp", next_Node.IP + ":" + strconv.Itoa(next_Node.Port)) //send the packet to the next node
				check_Error(err) //check for errors
				packet.Path_Traversed = append(packet.Path_Traversed, next_Node.Number)
				debug_Print("Node " + strconv.Itoa((*curr_Node).Number) + " sent a message to Node " + strconv.Itoa(next_Node.Number) + " \n")
				hops_Lock.Lock()
				hops++
				hops_Lock.Unlock()
				send_Msg(Packet{(*curr_Node).Number, end.Number, packet.Interest_Data, packet.Name, packet.Payload, packet.GP_Mode, packet.Nodes_Visit, packet.Num_Visit, packet.GP_Distance, packet.Path_Traversed, packet.Pressure_Gauge}, c)
			}
		}
	}
}
//----------------------------------------------

func main() {

	//----------------------------------------------
	//Step 0: For each topology
	//----------------------------------------------
	files, err := ioutil.ReadDir(data_Input)
	check_Error(err) //check for errors
	var global_Latency []float64 //measuring RTT
	var global_Packet_loss []float64 //seeing if packets get dropped at a local minimum
	var global_Stretch []float64 //comparing the forwarding algorithm path with dijkstra's path
	var global_Packet_size []float64 //the size of the packet
	var global_Extraneous_Hops []float64 //used to see if we have extra hops (hops after we deliver the packet)
	var global_Pressure_Percentage []float64 //percentage of packets that entered pressure mode
	var global_Pressure_Count []float64 //used to count number of hops made in pressure mode
	var global_Nodes_Visited []float64 //used to see the number of unique nodes visited
	for _, file_From_Files := range files{

		//----------------------------------------------
		//Step 1: Have the “driver” read in a topology file (see example below) that will list each node, with each node’s latitude, longitude, and neighbors
		//----------------------------------------------
		var topology []*Node //list of nodes in the topology
		file, err := os.Open(data_Input + file_From_Files.Name())// open file
		check_Error(err) //check for errors
		csvReader := csv.NewReader(file) //create a csvReader object

		// Read in the values line by line
		counter := -1 //to see how many items we have (-1 b/c increment on header)
		for {
			rec, err := csvReader.Read() //read the next line
			if err == io.EOF { //break out if its the end of the file
				break
			}
			if counter == -1{ //if the line we read in is the header or empty, skip it
				counter++
			} else{
				check_Error(err) //check for errors
				var neighbors []int //list of neighbors
				for x := 3; x < len(rec); x++{
					temp_int, err := strconv.Atoi(rec[x]) //cast to int
					check_Error(err) //check for errors
					if temp_int == 1{
						neighbors = append(neighbors, x-3) //append to the list
					}
				}
				temp_Number, err := strconv.Atoi(rec[0]) //cast string to int
				check_Error(err) //check for errors
				temp_Lat, err := strconv.ParseFloat(rec[1], 64) //cast string to flaot
				check_Error(err) //check for errors
				temp_Long, err := strconv.ParseFloat(rec[2], 64) //cast string to float
				check_Error(err) //check for errors
				temp_Node := &Node{IP: ip, Port: (port + counter), Number: temp_Number, Lat: temp_Lat, Long: temp_Long, Theta: -1.0, R: -1.0, Neighbors: neighbors} //create a struct for node
				topology = append(topology, temp_Node) //append to the list
				counter++
			}
		}
		file.Close() //close the file
		fmt.Println("Topology established for: " + file_From_Files.Name())
		//----------------------------------------------

		//----------------------------------------------
		//Step 2: The driver will then calculate the hyperbolic coordinates of each node, based off of the latitude and longitude
		//----------------------------------------------
		for x := 0; x < len(topology); x++{
			(*topology[x]).Theta = math.Atan((*topology[x]).Lat/(*topology[x]).Long)
			(*topology[x]).R = math.Sqrt(((*topology[x]).Lat*(*topology[x]).Lat) + ((*topology[x]).Long*(*topology[x]).Long))
		}
		fmt.Println("Hyperbolic coordinates calculated for: " + file_From_Files.Name())
		//----------------------------------------------

		//----------------------------------------------
		//Step 3: The driver will then set up a number of workers equal to the number of nodes in the topology
		// 	  Each worker will listen on its own port, and be assigned its hyperbolic coordinates
		//	  Also assign each server a PIT lock
		//----------------------------------------------
		shutdown_ACK := make(chan int, len(topology)) //channel for passing info
		packet_Contents := make(chan Packet, len(topology)) //channel for retrieving the return value
		for x := 0; x < len(topology); x++{
			var temp_Lock sync.Mutex
			topology[x].Lock = temp_Lock
			go setup_Node(topology[x], shutdown_ACK, packet_Contents, topology) //setup the nodes
		}
		//wait for all nodes to be setup
		for x := 0; x < len(topology); x++{
			<-shutdown_ACK
		}
		fmt.Println("All nodes setup for: " + file_From_Files.Name())
		//----------------------------------------------

		//----------------------------------------------
		//Step 4: The driver will then iteratively select a node combination for each node pairing in the topology
		//----------------------------------------------
		for x := 0; x < len(algorithms); x++{ //for each algorithm we want to test
			var latency []float64 //measuring RTT
			var packet_loss []float64 //seeing if packets get dropped at a local minimum
			var path_stretch []float64 //comparing the forwarding algorithm path with dijkstra's path
			var extraneous_Hops []float64 //used to see if we have extra hops (hops after we deliver the packet)
			var packet_size []float64 //the size of the packet
			var pressure_Percentage []float64 //percentage of packets in pressure mode
			var pressure_Count []float64 //hops made in pressure mode
			var nodes_Visited []float64 //used to see the number of unique nodes visited

			//Setup all node pairing
			for y := 0; y < len(topology)-1; y++{
				for z := y+1; z < len(topology); z++{
					start := find_Node(topology, y) //start node
					//----------------------------------------------
					//Step 5: For each node pairing, each forwarding algorithm will be used to send a packet across the topology based on those hyperbolic coordinates
					//----------------------------------------------
					curr_Algorithm = algorithms[x] //set the algorithm to the one we will be using
					hops = 0
					c, err := net.Dial("tcp", start.IP + ":" + strconv.Itoa(start.Port)) //Start by sending a packet to the start node
					check_Error(err) //check for errors
					open_Processes = 1
					debug_Print("Sending a message to Node " + strconv.Itoa(y) + " telling it to go to Node " + strconv.Itoa(z) +" \n")
					time_Start := time.Now() //start the timer right before sending packet over connection
					if algorithms[x] == "GF" || algorithms[x] == "mGF"{
						send_Msg(Packet{-1, z, 0, "/ucla/videos/demo.mpg/1/3", "" , -1, []int{}, []int{}, -1.0, []int{y}, -1}, c)
					} else{
						send_Msg(Packet{-1, z, 0, "/ucla/videos/demo.mpg/1/3", "" ,  0, []int{}, []int{}, -1.0, []int{y},  0}, c)
					}
					procees_Counter := 0
					lost_Packet := 0
					var return_Packets []Packet
					var timers []time.Time
					for procees_Counter < open_Processes{ //while processes are still active
						select{
							case return_Packet := <-packet_Contents: //grab the successful packet
                                                                timers = append(timers, time.Now())
                                                                lost_Packet = 1
								return_Packets = append(return_Packets, return_Packet) //in case we have multiple successful packets
								procees_Counter = procees_Counter + 1
							case _ = <-shutdown_ACK:
								procees_Counter = procees_Counter + 1
						}

					}
					debug_Print("Test for Node " + strconv.Itoa(y) + " and Node " + strconv.Itoa(z) +" done\n\n")
					packet_loss = append(packet_loss, float64(lost_Packet)) //0 if drop, 1 if success
					if len(return_Packets) == 0 && (algorithms[x] == "FILO_GPGF" || algorithms[x] == "ALL_GPGF" || algorithms[x] == "G_FILO_GPGF" || algorithms[x] == "G_ALL_GPGF" || curr_Algorithm == "FILO_GPmGF" || curr_Algorithm == "ALL_GPmGF" || curr_Algorithm == "G_FILO_GPmGF" || curr_Algorithm == "G_ALL_GPmGF"){
						fmt.Println("Error! Packet dropped for Gravity-Pressure")
						os.Exit(1)
					}

					if len(return_Packets) != 0{
						//First, figure out which packet is the one we are using (for multiple returns)
						//We will say to use the packet that arrived first (has the lowest time)
						time_Index := 0
						minimum_Time := timers[time_Index]
						for a := 1; a < len(timers); a++{
							if minimum_Time.After(timers[a]){
								minimum_Time = timers[a]
								time_Index = a
							}
						}
						return_Packet := return_Packets[time_Index]
						latency = append(latency, ((timers[time_Index]).Sub(time_Start)).Seconds()) //measures RTT only if success
						packet_size = append(packet_size, calc_Size(return_Packet))
						d_hops := dijkstras(y, z, topology) //calculate optimal hops
						RTT_d_hops := float64(d_hops*2) //multiplied by 2 because its to and from
						packet_Hops := float64(len(return_Packet.Path_Traversed)-1)
						path_stretch = append(path_stretch, packet_Hops/RTT_d_hops)
						extraneous_Hops = append(extraneous_Hops, (float64(hops)-packet_Hops)/float64(hops))
						nodes_Visited = append(nodes_Visited, float64(len(return_Packet.Nodes_Visit))/float64(len(topology)))
						if return_Packet.Pressure_Gauge > 0{ //we only want to look at algorithms that use pressure mode at least once
							pressure_Count = append(pressure_Count, float64(return_Packet.Pressure_Gauge)/dest_Hop(return_Packet.Path_Traversed, return_Packet.Destination))
							pressure_Percentage = append(pressure_Percentage, 1)
						} else{
							pressure_Percentage = append(pressure_Percentage, 0)
						}
						if algorithms[x] == "GF" || algorithms[x] == "mGF" || algorithms[x] == "FILO_GPGF" || algorithms[x] == "G_FILO_GPGF" || algorithms[x] == "FILO_GPmGF" || algorithms[x] == "G_FILO_GPmGF"{
							reverse_Check(return_Packet.Path_Traversed)
						}
						empty_PIT_Check(topology)
					}
					for a := 0; a < len(topology); a++{
						topology[a].Pit = []PIT{} //Set the default Pit values (should only be needed for dropped packets)
					}
				}
			}
			//----------------------------------------------
			//Step 6: An analysis will be calculated and output, showing things like latency, packet loss, path stretch per topology
			//GOlang is doing TRUNCATION, not ROUNDING - error of .001 at most
			//----------------------------------------------
			//fmt.Printf("\nPrinting results for: " + file_From_Files.Name() + "--" + algorithms[x] + " \n")
			//fmt.Printf("Average latency in seconds: %.7v\n", avg(latency))
			//fmt.Printf("Percentage of packets successfully delivered: %.4v%%\n", 100*(avg(packet_loss)))
			//fmt.Printf("Average path stretch: %.4v\n", avg(path_stretch))
			global_Latency = append(global_Latency, avg(latency))
			global_Packet_loss = append(global_Packet_loss, avg(packet_loss))
			global_Stretch = append(global_Stretch, avg(path_stretch))
			global_Packet_size = append(global_Packet_size, avg(packet_size))
			global_Extraneous_Hops = append(global_Extraneous_Hops, avg(extraneous_Hops))
			global_Pressure_Percentage = append(global_Pressure_Percentage, avg(pressure_Percentage))
			global_Pressure_Count = append(global_Pressure_Count, avg(pressure_Count))
			global_Nodes_Visited = append(global_Nodes_Visited, avg(nodes_Visited))
			fmt.Println("All tests complete for: " + file_From_Files.Name() + "--" + algorithms[x])
		}
		//----------------------------------------------
		//Step 7: Cleanup an experiment
		//----------------------------------------------
		//send the shutdown signal
		debug_Print("Sending shutdown signals\n")
		for x := 0; x < len(topology); x++{
			c, err := net.Dial("tcp", topology[x].IP + ":" + strconv.Itoa(topology[x].Port)) //Start by sending a packet to the start node
			check_Error(err) //check for errors
			send_Msg(Packet{Previous: -999, Destination: -999, Interest_Data: 2, Name: "Shutdown"}, c)
		}
		//wait for all nodes to shutdown
		for x := 0; x < len(topology); x++{
			<-shutdown_ACK
		}
		fmt.Printf("All nodes shutdown for: " + file_From_Files.Name() + "\n\n")
	}
	//----------------------------------------------
	//Step 7: An analysis will be calculated and output, showing things like latency, packet loss, path stretch averaged for all topologies
	//GOlang is doing TRUNCATION, not ROUNDING - error of .001 at most
	//----------------------------------------------
	fmt.Printf("-----------------------\n")
	var final_Values []float64
	for x := 0; x < len(algorithms); x++{
		var temp_Latency []float64
		var temp_Packet_loss []float64
		var temp_Stretch []float64
		var temp_Size []float64
		var temp_Extraneous_Hops []float64
		var temp_Pressure_Percentage []float64
		var temp_Pressure_Count []float64
		var temp_Nodes_Visited []float64
		for y := 0; y < len(global_Latency); y++{
			if y%len(algorithms) == 0+x{
				temp_Latency = append(temp_Latency, global_Latency[y])
				temp_Packet_loss = append(temp_Packet_loss, global_Packet_loss[y])
				temp_Stretch = append(temp_Stretch, global_Stretch[y])
				temp_Size = append(temp_Size, global_Packet_size[y])
				temp_Extraneous_Hops = append(temp_Extraneous_Hops, global_Extraneous_Hops[y])
				temp_Pressure_Percentage = append(temp_Pressure_Percentage, global_Pressure_Percentage[y])
				temp_Pressure_Count = append(temp_Pressure_Count, global_Pressure_Count[y])
				temp_Nodes_Visited = append(temp_Nodes_Visited, global_Nodes_Visited[y])
			}
		}
		//fmt.Printf("Printing results for: " + algorithms[x] + " \n")
		//fmt.Printf("%.4v\n", avg(temp_Latency))
		final_Values = append(final_Values, avg(temp_Latency))
		//fmt.Printf("%.4v\n", avg(temp_Size))
		final_Values = append(final_Values, avg(temp_Size))
		//fmt.Printf("%.4v%%\n", 100*avg(temp_Packet_loss))
		final_Values = append(final_Values, 100*avg(temp_Packet_loss))
		//fmt.Printf("%.4v\n", avg(temp_Stretch))
		final_Values = append(final_Values, avg(temp_Stretch))
		//fmt.Printf("%.4v%%\n", avg(temp_Extraneous_Hops))
		final_Values = append(final_Values, 100*avg(temp_Extraneous_Hops))
		//fmt.Printf("%.4v%%\n", avg(temp_Pressure_Percentage))
		final_Values = append(final_Values, 100*avg(temp_Pressure_Percentage))
		//fmt.Printf("%.4v%%\n", avg(temp_Pressure_Count))
		final_Values = append(final_Values, 100*avg(temp_Pressure_Count))
		//fmt.Printf("%.4v%%\n", avg(temp_Nodes_Visited))
		final_Values = append(final_Values, 100*avg(temp_Nodes_Visited))
		if x != len(algorithms)-1{
			fmt.Printf("\n")
		}
	}
	
	//Creating a file
	file, err := os.Create(output)
	check_Error(err)
	defer file.Close()
	
	for x := 0; x < len(algorithms); x++{
		fmt.Printf("\t" + algorithms[x])
		_, err = io.WriteString(file, "," + algorithms[x])
		check_Error(err)
	}
	fmt.Printf("\n")
	_, err = io.WriteString(file, "\n")
	check_Error(err)
	
	
	metric_names := []string{"Latency", "Packet Size", "Packet Loss", "Path Stretch", "Extraneous Hops", "Pressure percentage", "Pressure count", "Nodes visited"}
	for x := 0; x < len(metric_names); x++{
		fmt.Printf(metric_names[x] + "\t")
		_, err = io.WriteString(file, metric_names[x] + ",")
		check_Error(err)
		for y := x; y < len(final_Values); y=y+len(metric_names){	
			fmt.Printf("%.6v", final_Values[y])
			_, err = io.WriteString(file, strconv.FormatFloat(float64(final_Values[y]), 'f', -1, 64))
			check_Error(err)
			if y+len(metric_names) < len(final_Values){
				fmt.Printf("\t")
				_, err = io.WriteString(file, ",")
				check_Error(err)
			}
		}
		fmt.Printf("\n")
		_, err = io.WriteString(file, "\n")
		check_Error(err)
	}
	fmt.Printf("\n")
	check_Error(err)
	//----------------------------------------------

}

