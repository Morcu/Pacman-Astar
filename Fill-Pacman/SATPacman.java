package seguridad;


import org.jacop.core.BooleanVar;
import org.jacop.core.Store;
import org.jacop.jasat.utils.structures.IntVec;
import org.jacop.satwrapper.SatWrapper;
import org.jacop.search.DepthFirstSearch;
import org.jacop.search.IndomainMin;
import org.jacop.search.Search;
import org.jacop.search.SelectChoicePoint;
import org.jacop.search.SimpleSelect;
import org.jacop.search.SmallestDomain;
import java.util.*;
import java.lang.*;
import java.io.*;
public class SATPacman {
	

	public static void main(String args[]) throws IOException{
		Store store = new Store();
		SatWrapper satWrapper = new SatWrapper(); 
		store.impose(satWrapper);					/* Importante: sat problem */

		int nFantasma= Integer.parseInt(args[1]);
		//Leemos el archivo para busar cuantos muros hay 
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

		String b = "";
		String aux;
		int filas = a.size();
		int columnas = 0;
      		for(int i = 0; i < a.size(); i++){
          		for(int j = 0; j < a.get(i).size(); j++){
             			 b += a.get(i).get(j);
             			
             			 
         		 }
        	  b += "\n";
      		}
      		
      		
      		
      			//Se calcula el nuemro de columnas	
        columnas=((b.length()-filas)/filas);
      		BooleanVar [][] pacman= new BooleanVar[filas][columnas];  
      		BooleanVar [][][] fantasma= new BooleanVar[nFantasma][filas][columnas];	
          
      		for(int i = 0; i < a.size(); i++){
               	for(int j = 0; j < a.get(i).size(); j++){
               		for (int j2 = 0; j2 < columnas; j2++) {
					
               	//Declaracion de variables   
                  if(a.get(i).get(j).charAt(j2)!='%' && a.get(i).get(j).charAt(j2)!='O'){
                	  pacman[i][j2]= new BooleanVar(store,"\n Node p"+i +""+ j2);
                	for (int k = 0; k < fantasma.length; k++) {
                	  fantasma[k][i][j2]= new BooleanVar(store,"\n Node f"+k +i +""+ j2);
                	 }  
                  }
                  }		
                  			 
              	 }
           	}
      		
	
	  
	 // Se registran las variables
	    for (int i = 0; i < pacman.length; i++) {
			for (int j = 0; j < pacman[i].length; j++) {
				if(pacman[i][j]!= null)
				satWrapper.register(pacman[i][j]);
				
				for (int k = 0; k < fantasma.length; k++) {
					if(fantasma[k][i][j]!= null)
					satWrapper.register(fantasma[k][i][j]);
					
				}	
				
				
			}
		}
	    
	    
	 // Todas las variables en un unico array para despues invocar al metodo que nos
	 		// permite resolver el problema
	 		BooleanVar allVariables[] = new BooleanVar[2*nFantasma*filas*columnas];
	 		List variables = new ArrayList<>();
	 		
	 		
	 		for (int i = 0; i < pacman.length; i++) {
	 			for (int j = 0; j < pacman[i].length; j++) {
	 				if(pacman[i][j]!= null)
	 				variables.add(pacman[i][j]);
	 			}
	 		}
	 		for (int k = 0; k < fantasma.length; k++) {
		 		for (int i = 0; i < fantasma [k].length; i++) {
		 			for (int j = 0; j < fantasma[k][i].length; j++) {
		 				if(fantasma[k][i][j]!= null)
		 				variables.add(fantasma[k][i][j]);
		 			}
		 		}
	 		}
	 		
	 		allVariables = (BooleanVar[]) variables.toArray(new BooleanVar[variables.size()]);
	 		
	 	
	 		
	 		// 2. DECLARACION DE LOS LITERALES
	 		int pacmanLiteral[][] = new int[filas][columnas];
	 		int fantasmaLiteral[][][] = new int[nFantasma][filas][columnas];
	 		
	 			 		
	 		for (int i = 0; i < filas; i++) {
				for (int j = 0; j < columnas; j++) {
					if(pacman[i][j]!= null)
					pacmanLiteral[i][j] = satWrapper.cpVarToBoolVar(pacman[i][j],1, true);
					
				
				}
			}
	 		
	 		for (int k = 0; k < nFantasma; k++) {
		 		for (int i = 0; i < filas; i++) {
					for (int j = 0; j < columnas; j++) {
						if(fantasma[k][i][j]!= null)
							fantasmaLiteral[k][i][j] = satWrapper.cpVarToBoolVar(fantasma[k][i][j],1, true);
							
					}
		 		}

	 		}
	 		
	 		
	 	// 3. RESTRICCIONES
	 		
	 		
	 	addClause(satWrapper, pacmanLiteral);
						
		addClause(satWrapper, fantasmaLiteral);
	 		
	 	for (int k = 0; k < nFantasma; k++) {
		 	for (int x = 0; x < pacmanLiteral.length; x++) {
				for (int y = 0; y < pacmanLiteral[x].length; y++) {
					
					if((x-1)>0 && (y-1)>0 && (x+1)<filas && (y+1)<columnas){
						addClause(satWrapper, -pacmanLiteral[x][y], -fantasmaLiteral[k][x-1][y-1]);
						addClause(satWrapper, -pacmanLiteral[x][y], -fantasmaLiteral[k][x-1][y]);
						addClause(satWrapper, -pacmanLiteral[x][y], -fantasmaLiteral[k][x-1][y+1]);
						
						addClause(satWrapper, -pacmanLiteral[x][y], -fantasmaLiteral[k][x][y-1]);
						addClause(satWrapper, -pacmanLiteral[x][y], -fantasmaLiteral[k][x][y]);
						addClause(satWrapper, -pacmanLiteral[x][y], -fantasmaLiteral[k][x][y+1]);
						
						addClause(satWrapper, -pacmanLiteral[x][y], -fantasmaLiteral[k][x+1][y-1]);
						addClause(satWrapper, -pacmanLiteral[x][y], -fantasmaLiteral[k][x+1][y]);
						addClause(satWrapper, -pacmanLiteral[x][y], -fantasmaLiteral[k][x+1][y+1]);
					}
					
				}
			}	
	 	}
					
				
		
	 	//fantasmas en != filas
		 for (int i = 0; i < nFantasma; i++) {
			for (int i2 = 0; i2 < nFantasma; i2++) {
			 	for (int x = 0; x < filas; x++) {
					for (int y = 0; y < columnas; y++) {
						for (int k = 0; k < columnas; k++) {
							if(y != k && i!=i2)
							addClause(satWrapper,  -fantasmaLiteral[i][x][y], -fantasmaLiteral[i2][x][k]);
						}
					}
				}
		 	}	
		 }
		 //ESTO ESTA MAL EL SEGUNDOTIENE QUE TENER UN -
		//Restriccion para que se generen n fantanmas
		 
		 for (int i = 0; i < fantasmaLiteral.length; i++) {
			 for (int j = 0; j < fantasmaLiteral[i].length; j++) {
				for (int k = 0; k < fantasmaLiteral[i][j].length; k++) {
					for (int i2 = 0; i2 < fantasmaLiteral.length; i2++) {
						if(i!=i2)
						addClause(satWrapper, -fantasmaLiteral[i][j][k], -fantasmaLiteral[i2][j][k]);								
					}
				}
			}
		}
		 

		// 4. INVOCAR AL SOLUCIONADOR
		
	    Search<BooleanVar> search = new DepthFirstSearch<BooleanVar>();
		SelectChoicePoint<BooleanVar> select = new SimpleSelect<BooleanVar>(allVariables,new SmallestDomain<BooleanVar>(), new IndomainMin<BooleanVar>());
		Boolean result = search.labeling(store, select);

		if (result) {
			/*System.out.println("Solution: ");
			
			for (int i = 0; i < pacman.length; i++) {
				for (int j = 0; j < pacman[i].length; j++) {
					if(pacman[i][j]!= null)
					System.out.println(pacman[i][j].id() + " " + pacman[i][j].value());
				}
			}
			for (int k = 0; k < fantasma.length; k++) {
				for (int i = 0; i < fantasma[k].length; i++) {
					for (int j = 0; j < fantasmaLiteral[k][i].length; j++) {
											
					if(fantasma[k][i][j]!= null)
					System.out.println(fantasma[k][i][j].id() + " " + fantasma[k][i][j].value());
					}
				}
			}*/
			
			
			
			String imprimir = null;
			for (int i = 0; i < pacman.length; i++) {
				for (int j = 0; j < pacman[i].length; j++) {
					
					if(pacman[i][j]!= null){
						if(pacman[i][j].value()==1){
							imprimir= b.substring(0,(i*(columnas+1)+j)) + "P"+b.substring((i*(columnas+1)+j)+1);
						}
					}
				}
			}
			
			for (int k = 0; k < fantasma.length; k++) {
				for (int i = 0; i < fantasma[k].length; i++) {
					for (int j = 0; j < fantasmaLiteral[k][i].length; j++) {
						
						if(fantasma[k][i][j]!= null){				
							if(fantasma[k][i][j].value()==1){
								imprimir= imprimir.substring(0,(i*(columnas+1)+j)) + "G"+imprimir.substring((i*(columnas+1)+j)+1);
							}
						}
					}
				}
			}
			
			String fileName = args[0];
			String ficheroS = fileName.substring(0, fileName.length()-3); 
	    	ficheroS += "output";
	    	
	    	 File file =new File(ficheroS);
	    	 if(!file.exists()){
			       file.createNewFile();
			    }
	    	 FileWriter fw = new FileWriter(file);
			BufferedWriter writer = null;
			
			    writer = new BufferedWriter(fw);
			    writer.write(imprimir);
			    writer.close();
		} else{
			
			
			String fileName = args[2];
			String ficheroS = fileName.substring(0, fileName.length()-3); 
	    	ficheroS += "output";
	    	
	    	 File file =new File(ficheroS);
	    	 if(!file.exists()){
			       file.createNewFile();
			    }
	    	 FileWriter fw = new FileWriter(file);
			BufferedWriter writer = null;
			
			    writer = new BufferedWriter(fw);
			    writer.write("*** No solution");
			    writer.close();
		}

		System.out.println();
	}


	public static void addClause(SatWrapper satWrapper, int literal1, int literal2){
		IntVec clause = new IntVec(satWrapper.pool);
		clause.add(literal1);
		clause.add(literal2);
		satWrapper.addModelClause(clause.toArray());
	}


	public static void addClause(SatWrapper satWrapper, int literal1, int literal2, int literal3){
		IntVec clause = new IntVec(satWrapper.pool);
		clause.add(literal1);
		clause.add(literal2);
		clause.add(literal3);
		satWrapper.addModelClause(clause.toArray());
	}
	
	public static void addClause(SatWrapper satWrapper, int[][] literal){
		
		IntVec clause = new IntVec(satWrapper.pool);
				
		for (int i = 0; i < literal.length; i++) {
			for (int j = 0; j < literal[i].length; j++) {
				
				if(literal[i][j]>0){
				clause.add(literal[i][j]);
				}
			}
		}

		satWrapper.addModelClause(clause.toArray());
	}
	
	public static void addClause(SatWrapper satWrapper, int[][][] literal){
			
			IntVec clause;
			
			
			for (int k = 0; k < literal.length; k++) {
			clause = new IntVec(satWrapper.pool);
				for (int i = 0; i < literal[k].length; i++) {
					for (int j = 0; j < literal[k][i].length; j++) {
						
						if(literal[k][i][j]>0){
						clause.add(literal[k][i][j]);
						
						}
					}
				}
				satWrapper.addModelClause(clause.toArray());
			}
			
	}

}
