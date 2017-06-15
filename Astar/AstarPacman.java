package codigo;

import java.io.BufferedWriter;
import java.io.File;
import java.util.Arrays;
import java.util.List;
import java.io.FileWriter;
import java.io.IOException;
import java.io.PrintWriter;
import java.util.*;

//Objeto que contiene la informacion de los nodos
 class Cell{  
    int heuristicCost = 0; //coste heuristico
    int finalCost = 0; //G+H
    int i, j;
    Cell parent; 
    
    Cell(int i, int j){
        this.i = i;
        this.j = j; 
    }
    
    @Override
    public String toString(){
        return "["+this.i+", "+this.j+"]";
    }
}
 
//Clase java
public class AstarPacman {
    
	//Constantes de costes
    public static final int COSTE_CASILLA_VACIA = 4;
    public static final int COSTE_CASILLA_COMIDA = 2;
    
    //Grid de tipo Cell que guarda la informacion de cada nodo
    static Cell [][] grid;
    
    //Cola de abirto
    static PriorityQueue<Cell> open;
     
    static boolean closed[][];
    //Posicion inicial
    static int startI, startJ;
    
    //Posiciones final
    static int[] endX;
    static int [] endY;
    
    //Laberinto leido
    static char [][] laberinto;

    static int[][] fantasma;
    static int aux=2147483647; 
    static int contadorRuta=0; 
    static int costeTotal=0;
    
	//Numero de fantasmas y control de fantasmas ya comidos
    static int numFantasmas =0;
    static int numEnd;
    static int posPacX, posPacY, oldX, oldY;
    
    //Nombre de fichero de salida y array donde se guardan las estadisticas
    static String fileName;    
    static int [] estadisticas = new int[4];
   
    //Funcion que avisa de la posicion de un muro
    public static void setBlocked(int i, int j){
        grid[i][j] = null;
    }
    
    //Funcion que setea el nodo inicial
    public static void setStartCell(int i, int j){
        startI = i;
        startJ = j;
    }
    
	
    //Funcion que controla los estados finales
    public static void setEndCell(int x, int y){
    
    	endX[numFantasmas]=x;
    	endY[numFantasmas]=y;
    	numFantasmas++;
    	
    }
    
    //Funcion que comprueba, actualiza costes y anade a la lista de abierto
    static void checkAndUpdateCost(Cell current, Cell t, int cost){
        if(t == null || closed[t.i][t.j])return;
        int t_final_cost = t.heuristicCost+cost;
    
        boolean puede = false;
        boolean inOpen = open.contains(t);
        
        //Se controla que no se generen bucles 
        if(!inOpen || t_final_cost<t.finalCost){
        	Cell aux = current.parent;
        	while(aux!=null){
        	if(aux==t){
        		puede = true;
        		return;
        	}aux = aux.parent;
        	}
        	if (!puede) {
	            t.finalCost = t_final_cost;
	            t.parent = current;
	            if(!inOpen)open.add(t);
        	}
        }
       
    }
    
    //Algoritmo A* 
	public static boolean AStar(String heur) throws IOException   { 
    	//Anadimos el primer nodo en lista abierta
        open.add(grid[startI][startJ]);
        
        //Nodo actual
        Cell current;
        int contadorNodos=0;
        while(true){ 
        	//Obtine el primer elemento de la cola
            current = open.poll();
            //Si no es nulo se anade a la lista cerrada (se expande)
            if(current==null)break;
            closed[current.i][current.j]=true;
            contadorNodos++;
         

            //Se comprueba para todos los estados finales(fantasmas) si se ha llegado a un nodo meta
            for (int i = 0; i < numFantasmas; i++) {
            	
					//Si se ha llegado a un nodo meta se actualiza la informacion de los nodos meta
					if(current.equals(grid[endX[i]][endY[i]])){		
						
						//Si aun quedan fantasmas
						if (numFantasmas>0) {
							
							 //Se genera el ficherode salida
							String ficheroM = fileName.substring(0, fileName.length()-3); 
						    ficheroM += "output";
						    	
						    File file =new File(ficheroM);
	
						    //Si no existe el fichero se crea
						    if(!file.exists()){
						       file.createNewFile();
						    }
	
						    //Se crea un escritor que escribira a continuacion del fichero
						    FileWriter fw = new FileWriter(file,true);
						    //Se crea el BufferedWriter
						    BufferedWriter writer = new BufferedWriter(fw);
					
						    writer.append("PATH;");
						    open.add(current);
						    //Mientras exista nodo padre se escribe el recorrido desde nodo meta a nodo inicial
							while(current.parent!=null){
								
								
								//Se escriben "X" en el recorrido 
								if (laberinto[current.parent.i][current.parent.j] != 'P') {
									laberinto[current.parent.i][current.parent.j] = 'X';
					    			contadorRuta++;
								}	
		
								//Se escribe el path seguido
								writer.append(" -> "+current.parent);
								costeTotal +=current.finalCost;
								current = current.parent;
								
							} 
							
							writer.newLine();    
						    
							//Se escribe el laberinto en el fichero
						    for (int i1 = 0; i1 < laberinto.length; i1++) {
						    	for (int j = 0; j < laberinto[i1].length; j++) {
					    			writer.append(laberinto[i1][j]);
					    		}
						    	writer.newLine();
			   				}
						    writer.newLine();
						    
					    	writer.close();
		
							//EL fichero del laberinto para su escritura restaura a casillas vacias(" ") las casillas de "X"    
							for (int i1 = 0; i1 < laberinto.length; i1++) {
								for (int j = 0; j < laberinto[i1].length; j++) {
			    					if(laberinto[i1][j]=='X'||laberinto[i1][j]=='P'){
			    						laberinto[i1][j]=' ';
			    					}
			    				}
			    			}
							    	
							laberinto[endX[i]][endY[i]]='P';
				
							
							//Se actualiza el numero de fantasmas y sus respectivas posiciones en el array correspondiente
							int closX = closed.length;
							int closY = closed[0].length;
							closed = new boolean [closX][closY]; 
							
							current.i=endX[i];
							current.j=endY[i];
							    
							posPacX=endX[i];
							posPacY=endY[i];
							oldX=startI;
							oldY=startJ;
								
							int []auxX = new int[endX.length];
							System.arraycopy(endX, 0, auxX, 0, auxX.length);
							auxX[i]=auxX[auxX.length-1];
							endX = new int[auxX.length-1];
							for (int j = 0; j < endX.length; j++) {
								endX[j]=auxX[j];
							}
		
							int []auxY = new int[endY.length];
							System.arraycopy(endY, 0, auxY, 0, auxY.length);
							auxY[i]=auxY[auxY.length-1];
							endY = new int[auxY.length-1];
							for (int j = 0; j < endY.length; j++) {
								endY[j]=auxY[j];
							}
							estadisticas[3]+=contadorNodos;
							numEnd--;
							numFantasmas--;
							

							//Se actualizan las funciones heuristicas con un fantasma menos
							for(int z=1;z<grid.length;++z){
								for(int y=1;y<grid[z].length;++y){
									//Distancia de manhattan
									if(heur.equals("manhattan")){
										int coste;
				              			aux=2147483647;
				              			//Se calcula mediante la funcion la distancia y se guarda la menor entre todos los fantasmas
				              			for (int k = 0; k < numFantasmas; k++) {
											coste = Math.abs(z-endX[k])+Math.abs(y-endY[k]);
											if(coste<aux){
												aux= coste;
											}
								
									  }
				              			
				              			if(grid[z][y]!= null){
				              			grid[z][y].heuristicCost = aux;
				              			}
									}
									//Distancia euclidea
								  	if(heur.equals("euclidea")){
				                  		int coste;
				              			aux=2147483647;
				              			
				              			//Se calcula mediante la funcion la distancia y se guarda la menor entre todos los fantasmas
				              			for (int k = 0; k < numFantasmas; k++) {
											coste = (int) Math.sqrt((Math.pow(Math.abs(z-endX[k]),2.0)+Math.pow(Math.abs(y-endY[k]),2.0)));
				              				if(coste<aux){
												aux= coste;
											}
										}
				              				if(grid[z][y]!= null){
					              			grid[z][y].heuristicCost = aux;
					              			}
				                  	}
								}
							}
							 
							if(numFantasmas==0){
								//Si no quedan mas fantasmas y ha llegado a la solucion
					               return true;
						} 
						}else if(numFantasmas==0){
							//Si no quedan mas fantasmas y ha llegado a la solucion
				               return true;
					} 
				}		
           }
		
		
            Cell t;  
            //Comprobacion de los costes + las heuristicas de los posibles movimientos
            if(current.i-1>=0){
                t = grid[current.i-1][current.j];
                //Si hay una comida el coste es distinto de si la casilla esta vacia
               if(laberinto[current.i-1][current.j] == 'O'){
            	   checkAndUpdateCost(current, t, current.finalCost+COSTE_CASILLA_COMIDA); 
               }else{
                checkAndUpdateCost(current, t, current.finalCost+COSTE_CASILLA_VACIA); 
               }
                
            }

            if(current.j-1>=0){
                t = grid[current.i][current.j-1];
                if(laberinto[current.i][current.j-1] == 'O'){
             	   checkAndUpdateCost(current, t, current.finalCost+COSTE_CASILLA_COMIDA); 
                }else{
                 checkAndUpdateCost(current, t, current.finalCost+COSTE_CASILLA_VACIA); 
                }
            }

            if(current.j+1<grid[0].length){
                t = grid[current.i][current.j+1];
                if(laberinto[current.i][current.j+1] == 'O'){
             	   checkAndUpdateCost(current, t, current.finalCost+COSTE_CASILLA_COMIDA); 
                }else{
                 checkAndUpdateCost(current, t, current.finalCost+COSTE_CASILLA_VACIA); 
                }
            }

            if(current.i+1<grid.length){
                t = grid[current.i+1][current.j];
                if(laberinto[current.i+1][current.j] == 'O'){
             	   checkAndUpdateCost(current, t, current.finalCost+COSTE_CASILLA_COMIDA); 
                }else{
                 checkAndUpdateCost(current, t, current.finalCost+COSTE_CASILLA_VACIA); 
                }
                
            }
        
            
        }
        if(numFantasmas>0){
        	return false; 
        }
        if(numFantasmas==0){
        	return true; 
        }
        return true;
    }
    
   
    public static void Ejecutar(int tCase, int x, int y, String heuristica) throws IOException{
          
           //Se crea el grid sobre el que se va a trabajar la lista de cerrado y la cola de abierta
           grid = new Cell[x][y];
           closed = new boolean[x][y];
           open = new PriorityQueue<>((Object o1, Object o2) -> {
                Cell c1 = (Cell)o1;
                Cell c2 = (Cell)o2;

                return c1.finalCost<c2.finalCost?-1:
                        c1.finalCost>c2.finalCost?1:0;
            });
    
           //Se obtienen las posiciones iniciales y finales del laberito (pacman y fantasma respectivamente)
           char elector;
           int inicialPosX=0, inicialPosY=0;
           for (int i = 0; i < laberinto.length; i++) {
    			for (int j = 0; j < laberinto[i].length; j++) {
    				elector = laberinto[i][j];
    				switch (elector) {
    				//Posicion inicial (pacman)
    				case 'P':
    					//Posicion inicial en el grid
    					setStartCell(i, j);
    					inicialPosX=i;
    					inicialPosY=j;
    					break;
    				//Posicion final (fantsama)
    				case 'G':
    					//Posicion final en el grid
    					setEndCell(i, j);
    					break;
    				}
    			}
    		}

           for(int i=0;i<x;++i){
              for(int j=0;j<y;++j){
            	  //Generamos todas las casillas del grid
                  grid[i][j] = new Cell(i, j);
                  
                	   //Se elige entre la distancia de manhattan y la distancia euclidea como heuristicas
                  	if(heuristica.equals("manhattan")){
                  		int coste;
              			aux=2147483647;
              			
              			//Distancia de manhattan
              			for (int k = 0; k < numFantasmas; k++) {

							coste = Math.abs(i-endX[k])+Math.abs(j-endY[k]);
							
							if(coste<aux){
								aux= coste;
							}
						}
							grid[i][j].heuristicCost = aux;
                  	}
                  	
 
                  	if(heuristica.equals("euclidea")){
                    	//Distancia de euclidea
                  		int coste;
              			aux=2147483647;
              			
              			//Distancia de manhattan
              			for (int k = 0; k < numFantasmas; k++) {

							coste = (int) Math.sqrt((Math.pow(Math.abs(i-endX[k]),2.0)+Math.pow(Math.abs(j-endY[k]),2.0)));
              				if(coste<aux){
								aux= coste;
							}
					    }
							grid[i][j].heuristicCost = aux;
                  	}
				
              }
           }
           
           
           //Anadimos los muros en el grid
           for (int i = 0; i < laberinto.length; i++) {
    			for (int j = 0; j < laberinto[i].length; j++) {
    				elector = laberinto[i][j];
    				switch (elector) {
    				//Muro	
    				case '%':
    					setBlocked(i, j);
    					break;
    				}
    			}
    		}
           
           
        
         //LLamamos a la funcion que genera el algoritmo A*
         boolean ret =  AStar(heuristica); 
       
         //Si no hay solucion
         if(ret==false){
    		 //Se genera el ficherode salida
				String ficheroM = fileName.substring(0, fileName.length()-3); 
			    ficheroM += "output";
			    	
			    File file =new File(ficheroM);

			    //Si no existe el fichero se crea
			    if(!file.exists()){
			       file.createNewFile();
			    }

			    //Se crea un escritor que escribira a continuacion del fichero
			    FileWriter fw = new FileWriter(file,true);
			    //Se crea el BufferedWriter
			    BufferedWriter writer = new BufferedWriter(fw);
			    	
		
			    writer.append("No es posible encontrar solucion");
			    writer.close();
        	 
         }
                    
         estadisticas[2]+=contadorRuta;
         estadisticas[1] += costeTotal;
                    
                   
         //Se vuelvena a actualizar las casillas que se han marcado con una X para mostrar el camino del pacman
         for (int k = 0; k < laberinto.length; k++) {
        	 for (int l = 0; l < laberinto[k].length; l++) {
				if (laberinto[k][l]=='X') {
					laberinto[k][l]=' ';
				}
			}
		}
                    
                    laberinto[oldX][oldY]=' ';
                    laberinto[posPacX][posPacY]='P';
                    numFantasmas=0;
                   
}
    
    
     
    public static void main(String[] args) throws Exception{   
    	long tiempoI = System.currentTimeMillis();
    	
    	fileName = args[0];
    	
    	
    	//Leer el laberinto
    	ArrayList<ArrayList<String>> a = new ArrayList<ArrayList<String>>();
		Scanner input = new Scanner(new File(args[0]));
		while(input.hasNextLine())
		{
		    Scanner colReader = new Scanner(input.nextLine());
		    ArrayList<String> col = new ArrayList<String>();
		    while(colReader.hasNextLine())
		    {
			col.add(colReader.nextLine());
		    }
		    a.add(col);
		}
		
		
		//Obtener el numero de filas
		String b = "";
		int filas = a.size();
		int columnas = 0;
      		for(int i = 0; i < a.size(); i++){
          		for(int j = 0; j < a.get(i).size(); j++){
             			 b += a.get(i).get(j);
         		 }
        	  b += "\n";
      		}
      		
       //Se calcula el numero de columnas	
       columnas=((b.length()-filas)/filas);
        
       int numeroF =0;
        //Se genera el laberinto 
       char[] aCaracteres = b.toCharArray();
       laberinto = new char[filas][columnas];
  
       for (int i = 0; i < laberinto.length; i++) {
			for (int j = 0; j < laberinto[i].length; j++) {
				
				laberinto[i][j] = aCaracteres[j+((columnas+1)*i)];
				if (laberinto[i][j]=='G') {
					numeroF++;
				}
			}
			
		}
       
       endX = new int [numeroF];
       endY = new int [numeroF];
       numEnd = numeroF;
       
	fantasma = new int [numeroF][numeroF];
       
       
       //Se limpia el fichero de salida para que este vacio a la hora de escribir
      try {
		
    	  String ficheroM = fileName.substring(0, fileName.length()-3); 
		  ficheroM += "output";
	    	
		  FileWriter fW = new FileWriter(ficheroM, false);
		  PrintWriter pW = new PrintWriter(fW,false);
		  pW.flush();
		 
		  fW.close();
		  pW.close();
		  
		  String ficheroStaticstics = fileName.substring(0, fileName.length()-3); 
		  ficheroStaticstics += "statistics";
		  FileWriter fWS = new FileWriter(ficheroStaticstics, false);
		  PrintWriter pWS = new PrintWriter(fWS,false);
		  pWS.flush();
		  fWS.close();
		  pWS.close();

	} catch (Exception e) {
		//System.out.println("Error al limpiar fichero de salida");
	}  
		  
      //Se llama al metodo de ejecucion al que se le pasa el numerode test el numero de filas y columnas del laberinto y 
      //la heuristica a utilizar, en este caso la heuristica se pasa por parametro
       Ejecutar(1, filas, columnas, args[1]);
       
        //Se calcula el tiempo de ejecucion
        long tiempoF = System.currentTimeMillis();
        int totalTiempo = (int) (tiempoF - tiempoI);
        
        estadisticas[0] = totalTiempo;

    	String ficheroS = fileName.substring(0, fileName.length()-3); 
    	ficheroS += "statistics";
    	
    	
    	BufferedWriter writer = null;
    	//Se escriben las estadisticas en su fichero correspondiente
		try{
		    writer = new BufferedWriter( new FileWriter(ficheroS));
		    writer.write( "Tiempo total: " + estadisticas[0]+" ms");
		    writer.newLine();
		    writer.write( "Coste total: " + estadisticas[1]);
		    writer.newLine();
		    writer.write( "Longitud de la ruta: " + estadisticas[2]);
		    writer.newLine();
		    writer.write( "Nodos expandidos: " + estadisticas[3]);
		    
		    
		}//Control de errores
		catch ( IOException e){}
		finally{
		    try{
		        if ( writer != null)
		        writer.close( );
		    }
		    catch ( IOException e){}
		}
    }
}
