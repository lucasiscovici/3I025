# -*- coding: utf-8 -*-

# Nicolas, 2015-11-18

from __future__ import absolute_import, print_function, unicode_literals
from gameclass import Game,check_init_game_done
from spritebuilder import SpriteBuilder
from players import Player
from sprite import MovingSprite
from ontology import Ontology
from itertools import chain
import pygame
import glo

import random 
import numpy as np
import sys
import heapq
import operator


class Astar():

    def __init__(self,pb):
        self.depart=pb[0]
        self.arrivee=pb[1]
        self.wallStates=pb[2]

    def manhattan(self, depart, arrivee):
        (x1, y1), (x2, y2) = depart, arrivee
        return abs(x2-x1) + abs(y2-y1)
        
        
    def astar(self):
        depart = self.depart
        arrivee = self.arrivee
        frontiere = [(0, 0, depart, None)]
        reserve = {}
        (row,col) = depart
        
        while frontiere != [] and (row,col)!=arrivee:
            
            _, previous_g, (row,col), pere = heapq.heappop(frontiere)
            if (row,col) not in reserve:
                reserve[(row,col)] = pere
                for (x_inc, y_inc) in [(0,1),(0,-1),(1,0),(-1,0)]:
                   next_row = row+x_inc
                   next_col = col+y_inc 
                   if ((next_row,next_col) not in self.wallStates) and next_row>=0 and next_row<=19 and next_col>=0 and next_col<=19:
                       f = previous_g+1 + self.manhattan((next_row,next_col), arrivee)
                       heapq.heappush(frontiere, (f, previous_g+1, (next_row,next_col), (row,col)))
                       
        res = []               
        (row,col) = arrivee
        while (row,col) != depart:
            res.insert(0, (row,col))
            (row,col) = reserve[(row,col)]
            
        return res
class Astar2():

    def __init__(self,pb,me=0):
        self.pb = pb
        self.depart=pb[0][me]
        self.wallStates=pb[2]
        #print(self.pb)
        #self.closer()

    def closer(self):
        tab=[]
        for i in self.pb[1]:
            tab.append(Astar([self.depart,i,self.wallStates]).astar())
        if len(tab)==0:
            return []
        return tab[sorted([(i,len(v)) for i,v in enumerate(tab)],key=lambda d:d[1])[0][0]]
    
class SimuT():
        def __init__(self, p):
            self.p = p
            self.fioles={0:{},1:{}}
            self.fiole = []
            for (i,j,k,l) in p:
                self.fioles[i][j]=[k,l];
                if j not in self.fiole:
                    self.fiole.append(j);
                

        def chemin_with_id(self,id,fid):
            return self.fioles[id][fid];

        def compare(self,fid):
            return self.chemin_with_id(0,fid)[0] <=  self.chemin_with_id(1,fid)[0]


points={'b':2,'j':6,'r':10}  
points2={'b':6,'j':10,'r':2} 
pt={0:points,1:points2} 
maxo = 3;
def f_in_astar(a,fiole):
    aa=[]
    for i in a[:-1]:
        if i in fiole:
            aa.append(fiole.index(i))
    return aa

def less(f,id):
    return [(i,v) for (i,v) in f if (i,v) != id]

def lessa(f,ids):
    return [(i,v) for (i,v) in f if (i,v) not in ids]

    
class simul():

    def __init__(self, pb,fioles,pc=1,decal=""):
        #print()
       # print("------------"+str(pc)+"---------------")
        self.pb = pb

        #print(decal+"sumul init pb => ",pb[0],pb[1])
        self.fiole=fioles
        #print(decal+str(self.fiole));

       # print("simul init fiole => ",self.fiole)
        self.initial = self.init()
        p=self.initial;
        #print("simul init initial => ",p)
        self.sim = SimuT(p);
        #print("simul init sim => ",self.sim)
        self.fioless = []
        for i in self.sim.fiole:
            self.fioless.append(self.pb[1][i])
        self.pc = pc;
        self.decal=decal;
        self.pt=0
        #print(self.decal+str(self.fioless));
    

    #te renvoit un vecteur avec i(indice du joeur dans pb0) j (indice de la fiole dans pb1), len(A*),A*
    def init(self):
        
        # f est un tableau de tupple (i,j,len(A*),A*)
        f = [(i,j,len(Astar([v,w,self.pb[2]]).astar()),Astar([v,w,self.pb[2]]).astar()) for i,v in enumerate(self.pb[0]) for j,w in enumerate(self.pb[1]) ];
        f2 = [i for i in f if i[0]==0]
        f3 = sorted(f2, key=lambda t:t[2])
        f4 = [v for (i,v,h,d) in f3[:maxo]]
        f5 = [i for i in f if i[1] in f4]
        return f5;


    def new_pb(self,fid,fid2):
        pb=[]
        inits=[]
        goal=[]
        astar0 = self.sim.chemin_with_id(0,fid);
        astar1 = self.sim.chemin_with_id(1,fid2);
        gfid=fid
        gfidt=[gfid]
        if astar0[0] < astar1[0]:
            inits.append(self.pb[1][fid])
            inits.append(astar1[1][astar0[0]-1])
            bg=f_in_astar(astar0,self.pb[1])
            bg2=f_in_astar(astar1,self.pb[1])
            h=list(set(bg + bg2))
            gfidt= list(set(gfidt + h))
        else:
            diff=astar0[0] - astar1[0]
            diff2=diff
            inits.append(self.pb[1][fid])
            b=[]
            bg3=[]
            u=less(self.fioless,self.pb[1][fid2])
            fm=self.pb[1][fid2]
            ax=None
            while diff2>0:
                b= Astar2([[fm],u,self.pb[2]]).closer();
                if len(b)>0:
                    bg3+=f_in_astar(b[:diff2],self.pb[1])
                    if diff2 >= len(b):
                        ax=b[-1]
                    else:
                        ax=b[diff2-1]
                    u=lessa(u,bg3)
                    fm=b[-1]
                    diff2-=len(b)
                else:
                    break
            if len(b)>0 or ax != None:
                inits.append(ax)
            else:
                inits.append(self.pb[1][fid2])

            bg=f_in_astar(astar0,self.pb[1])
            bg2=f_in_astar(astar1,self.pb[1])
            if len(b)>0:
                bg3+=f_in_astar(b[:diff],self.pb[1])
            h=list(set(bg + bg2 + bg3))
            gfidt= list(set(gfidt + h))

        goal=[(i,v) for u,(i,v) in enumerate(self.pb[1]) if (i,v) in self.fioless and u not in gfidt]
        walls = self.pb[2]
        return [inits,goal,walls]

  #point -> pourcentage en fonction de la distance 
    def point(self,ii):
        fg = self.pc
        fiolen = self.fiole
        self.pt=0
        if self.sim.compare(ii):
            #print(self.decal+"+"+str(self.pc)+" "+str(points[self.fiole[self.pb[1][ii]]]))
            #print("simulation de",ii,"je suis plus pres")
            fg*=points[self.fiole[self.pb[1][ii]]]
            #print(self.decal+str(fg))

        astar0=self.sim.chemin_with_id(0,ii);
        bg=f_in_astar(astar0,self.pb[1])
        for h in bg:
            self.pt+=points[self.fiole[self.pb[1][h]]]
        #print("fiole =>",self.sim.fiole)
        #print("fiolen =>",fiolen)
        nea={i:self.sim.chemin_with_id(1,i)[0] for i in self.sim.fiole }
        nea = sorted(nea.items(),key=operator.itemgetter(1))
        nea ={i:v for (i,v) in nea}
        nea = {nea.keys()[i]:i for i in range(len(nea))}
        s=[simul(self.new_pb(ii,i),self.fiole,(1-((nea[i]+1)/len(self.sim.fiole))),self.decal+" ").simulation()[1] for i in self.sim.fiole ]
        #print("pt-simu => ",s)
        f = fg + sum(s) + self.pt 
       # print(self.decal+"sommePT= "+str(f))
        return f


  #point 1 -> pourcentage equiprobable
    def point1(self,ii):
        fg = self.pc
        fiolen = self.fiole
        self.pt=0
        if self.sim.compare(ii):
            #print(self.decal+"+"+str(self.pc)+" "+str(points[self.fiole[self.pb[1][ii]]]))
            #print("simulation de",ii,"je suis plus pres")
            fg*=points[self.fiole[self.pb[1][ii]]]
            #print(self.decal+str(fg))

        astar0=self.sim.chemin_with_id(0,ii);
        bg=f_in_astar(astar0,self.pb[1])
        for h in bg:
            self.pt+=points[self.fiole[self.pb[1][h]]]
        #print("fiole =>",self.sim.fiole)
        #print("fiolen =>",fiolen)
   
        s=[simul(self.new_pb(ii,i),self.fiole,1/len(self.sim.fiole),self.decal+" ").simulation()[1] for i in self.sim.fiole ]
        #print("pt-simu => ",s)
        f = fg + sum(s) + self.pt 
       # print(self.decal+"sommePT= "+str(f))
        return f

    #simulation avec point et pourcentage equiprobable
    def simulation(self):
        
        simu = {};
        somme=0;
        for i in self.sim.fiole:
            #print(self.decal+"sumulation de",i,self.pb[1][i]);
            a=self.point(i)
            simu[i]=a
            somme+=a

        return [simu,somme];

    #simulation1 avec point1 et pourcentage en fonction de la distance
    def simulation1(self):
        
        simu = {};
        somme=0;
        for i in self.sim.fiole:
            #print(self.decal+"sumulation de",i,self.pb[1][i]);
            a=self.point1(i)
            simu[i]=a
            somme+=a

        return [simu,somme];


    #simulationf avec simulation 
    #trouve la fiole la plus bonne et retourne le a* 
    def simulationf(self):
        
        f= self.simulation()
        fid=sorted(f[0].items(),key=operator.itemgetter(1),reverse=True)[0][0]

        return [ l for i,j,k,l in self.initial if i==0 and j==fid][0]

    #simulationf1 avec simulation1
    def simulationf1(self):
        
        f= self.simulation1()
        fid=sorted(f[0].items(),key=operator.itemgetter(1),reverse=True)[0][0]

        return [ l for i,j,k,l in self.initial if i==0 and j==fid][0]
      # h = []
        # g = []

        # for ii in range(n):
        #     point=0
        #     g = [(j,k) for i,j,k in astars if j==ii]
        #     print(g)
        #     if(g[o][1]<g[abs(o-1)][1]):
        #         point+=pt(h[g[0][0]])*po
        #     else:
        #         point+=simulation()


    
# ---- ---- ---- ---- ---- ----
# ---- Main                ----
# ---- ---- ---- ---- ---- ----

game = Game()

def init(_boardname=None):
    global player,game
    # pathfindingWorld_MultiPlayer4
    name = _boardname if _boardname is not None else 'match2'
    game = Game('Cartes/' + name + '.json', SpriteBuilder)
    game.O = Ontology(True, 'SpriteSheet-32x32/tiny_spritesheet_ontology.csv')
    game.populate_sprite_names(game.O)
    game.fps = 10  # frames per second
    #game.mainiteration()
    game.mask.allow_overlaping_players = True
    #player = game.player
    
def main():
    pol=0
    scores=[0,0];
    scores1=[0,0];
    score_old=[]
    fio = []
    jk=0
    while True:
        #for arg in sys.argv:
        iterations = 200 # default
        if len(sys.argv) == 2:
            iterations = int(sys.argv[1])
        #print ("Iterations: ")
        #print (iterations)

        init()
        
        
        

        
        #-------------------------------
        # Initialisation
        #-------------------------------
           
        players = [o for o in game.layers['joueur']]
        #players = [players[1],players[0]]
        nbPlayers = len(players)
        score = [0]*nbPlayers
        score1 = [0]*nbPlayers

        fioles = {} # dictionnaire (x,y)->couleur pour les fioles
        
        
        # on localise tous les états initiaux (loc du joueur)
        initStates = [o.get_rowcol() for o in game.layers['joueur']]
      #  print ("Init states:", initStates)
        #initStates = [initStates[1],initStates[0]]
        
        # on localise tous les objets ramassables
        #goalStates = [o.get_rowcol() for o in game.layers['ramassable']]
            
        # on localise tous les murs
        wallStates = [w.get_rowcol() for w in game.layers['obstacle']]
       # print ("Wall states:", wallStates)
        
        #-------------------------------
        # Placement aleatoire des fioles de couleur 
        #-------------------------------
        if jk%2!=0:
            pm=0
            for o in game.layers['ramassable']: # on considère chaque fiole
                p=fio[pm][1]
                fioles[fio[pm][0][0]]=fio[pm][0][1]
                game.layers['ramassable'].remove(o)
                game.layers['ramassable'].add(p)
                pm+=1
        else:
            fio=[]
            for o in game.layers['ramassable']: # on considère chaque fiole
                
                #on détermine la couleur
            
                if o.tileid == (19,0): # tileid donne la coordonnee dans la fiche de sprites
                    couleur = "r"
                elif o.tileid == (19,1):
                    couleur = "j"
                else:
                    couleur = "b"

                # et on met la fiole qqpart au hasard

                x = random.randint(1,19)
                y = random.randint(1,19)

                while (x,y) in wallStates or (x,y) in fioles: # ... mais pas sur un mur
                    x = random.randint(1,19)
                    y = random.randint(1,19)
                o.set_rowcol(x,y)
                # on ajoute cette fiole 
                fioles[(x,y)]=couleur
                fio.append((((x,y),couleur),o))
                game.layers['ramassable'].add(o)
            #game.mainiteration()                
        
        print("Les fioles ont été placées aux endroits suivants: \n", fioles)

        #game.mainiteration()                

        #-------------------------------
        # Boucle principale de déplacements 
        #-------------------------------
        goalStates = [o.get_rowcol() for o in game.layers['ramassable']]
        print ("Goal states:", goalStates)

            
        # bon ici on fait juste plusieurs random walker pour exemple...
        posPlayers = initStates
        probleme = [initStates,goalStates,wallStates]
        #print("debut simul => ");
        # print(simul(probleme,fioles).simulation());
        it=simul(probleme,fioles).simulationf()
        #it = Astar2(probleme).closer()
        oo=0
        if jk%2==0:
            print("sumul")
        else:
            print("simul1")
        for i in range(iterations):
            #raw_input();
            if len(fioles)==0:
                    break;
            for j in range(nbPlayers): # on fait bouger chaque joueur séquentiellement
                goalStates = [o.get_rowcol() for o in game.layers['ramassable'] if o.get_rowcol() in fioles]
                initStates = posPlayers
                probleme = [initStates,goalStates,wallStates]
                if j==0:
                    row,col = posPlayers[j]
                    #
                    if jk%2==0:
                        it=simul([initStates,goalStates,wallStates],fioles).simulationf()
                        #it=Astar2(probleme,0).closer()
                    else:
                        #it=Astar2(probleme,0).closer();
                        it=simul([initStates,goalStates,wallStates],fioles).simulationf1()
                    next_row = row if len(it)==0  else it[oo][0]
                    next_col = col if len(it)==0 else it[oo][1]
                    oo=0
                    # and ((next_row,next_col) not in posPlayers)
                    if ((next_row,next_col) not in wallStates) and next_row>=0 and next_row<=19 and next_col>=0 and next_col<=19:
                        players[j].set_rowcol(next_row,next_col)
                        #print ("pos :", j, next_row,next_col)
                        #game.mainiteration()
            
                        col=next_col
                        row=next_row
                        posPlayers[j]=(row,col)
                else:
                    row,col = posPlayers[j]
                    dx = Astar2(probleme,1).closer();
                    #dx =simul([initStates[::-1],goalStates,wallStates],fioles).simulationf()
                    next_row =  row if len(dx)==0 else dx[0][0]
                    next_col = col if len(dx)==0 else  dx[0][1]
                    # and ((next_row,next_col) not in posPlayers)
                    if ((next_row,next_col) not in wallStates) and next_row>=0 and next_row<=19 and next_col>=0 and next_col<=19:
                        players[j].set_rowcol(next_row,next_col)
                        #print ("pos :", j, next_row,next_col)
                        #game.mainiteration()
            
                        col=next_col
                        row=next_row
                        posPlayers[j]=(row,col)
                    
              
            
                
                # si on a  trouvé un objet on le ramasse
                if (row,col) in fioles:
                    o = players[j].ramasse(game.layers)
                    #print ("Objet de couleur ", fioles[(row,col)], " trouvé par le joueur ", j)
                    if jk%2==0:
                        score[j]+=pt[j][fioles[(row,col)]]             # il faudra adapter aux préférences!
                        print(j,score[j],score)
                    else:
                        score1[j]+=pt[j][fioles[(row,col)]]
                        print(j,score1[j],score)
                    fioles.pop((row,col))   # on enlève cette fiole de la liste
                game.mainiteration()
                if len(fioles)==0:
                    break;
                     
                

                    #break
                
        if jk%2!=0:
            print ("scores:", score_old)
            print ("scores1:", score1)
        else:
            print ("scores:", score)
            score_old=score


       # print (fioles)
        pol+=1
        if jk%2==0:
            scores=[scores[0]+score[0],scores[1]+score[1]]
        else:
            scores1=[scores1[0]+score1[0],scores1[1]+score1[1]]
        jk+=1
        if pol==8:
            game.mainiteration()
            pygame.quit()
            break;
    
        
    print(scores);
   

if __name__ == '__main__':
    main()
    


