/* Copyright (c) 1997-2015
   Ewgenij Gawrilow, Michael Joswig (Technische Universitaet Berlin, Germany)
   http://www.polymake.org

   This program is free software; you can redistribute it and/or modify it
   under the terms of the GNU General Public License as published by the
   Free Software Foundation; either version 2, or (at your option) any
   later version: http://www.gnu.org/licenses/gpl.txt.

   This program is distributed in the hope that it will be useful,
   but WITHOUT ANY WARRANTY; without even the implied warranty of
   MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
   GNU General Public License for more details.
--------------------------------------------------------------------------------
*/
#include <cmath>
#include "polymake/Matrix.h"
#include "polymake/linalg.h"
#include "polymake/Vector.h"
#include "polymake/Set.h"
#include "polymake/GenericMatrix.h"
#include "polymake/pair.h"
#include "polymake/internal/operations.h"


#include <algorithm>
#include <tuple>

namespace pm {

namespace {
   const double epsilon=1e-14; // machine epislon

   struct matrixTriple {Matrix<double> diag; Matrix<double> left; Matrix<double> right;};
   struct matrixPair {Matrix<double> left; Matrix<double> right;};

   int non_zero_sign(const double v)
   {
      int s=sign(v);
      if (s==0) {
         s=1;
      }
      return s;
   }

  matrixTriple  bidiag(Matrix<double> M)
  {
  // bidiagonalization algorithm  using householder transformations
     const int colsM=M.cols()-1;  
     const int rowsM=M.rows()-1;
     Matrix<double> U=unit_matrix<double>(rowsM+1);
     const int dimU=U.rows()-1;
     Matrix<double> V=unit_matrix<double>(colsM+1);
     const int dimV=V.rows()-1;
     for (int i=0; i<=std::min(rowsM,colsM); i++) // check "<"
        {
    
           const Vector<double>v=M.col(i).slice(i);
           const Matrix<double>Ui=householder_trafo(v);
           const Matrix<double>M1=non_zero_sign(v[0])*Ui*M.minor(range(i,rowsM),range(i,colsM));
           M.minor(range(i,rowsM),range(i,colsM))=M1;
           const Matrix<double>U1=non_zero_sign(v[0])*Ui*U.minor(range(i,dimU),range(0,dimU)); 
           U.minor(range(i,dimU),range(0,dimU))=U1;
    
           if (i<=colsM-2){
              const Vector<double>v=M.row(i).slice(i+1);
              const Matrix<double>Vi=householder_trafo(v);
              const Matrix<double>M1=non_zero_sign(v[0])*M.minor(range(i,rowsM),range(i+1,colsM))*Vi;
              M.minor(range(i,rowsM),range(i+1,colsM))=M1;
              const Matrix<double>V1=non_zero_sign(v[0])*V.minor(range(0,dimV),range(i+1,dimV))*Vi;
              V.minor(range(0,dimV),range(i+1,dimV))=V1;
           }
        } 
     matrixTriple bidiagonalMatrixTriplet; 
     bidiagonalMatrixTriplet.diag=M;
     bidiagonalMatrixTriplet.left=U;
     bidiagonalMatrixTriplet.right=V;
     return bidiagonalMatrixTriplet;
  }


   Matrix<double> givens_rot(Vector<double> v)
  // elementray 2x2 given rotation algorithm
   {
	//U is a unitary transformation matrix
      Matrix<double> U(2,2);

      double abs_val=sqrt(v[0]*v[0]+v[1]*v[1]);     
      if (abs(v[0])<epsilon){
            U[0][0]=0;
            U[0][1]=1;
            U[1][0]=1;
            U[1][1]=0; 
         }
      else{
      const double c=v[0]/(sign(v[0])*abs_val);
      const double s=-v[1]/(sign(v[0])*abs_val);
      U[0][0]=c;
      U[0][1]=s;
      U[1][0]=-s;
      U[1][1]=c;      
      }     
      return U;
   }
}

   double eigenValuesOfT(double dm, double dn, double fm, double fmMinus1 )
   {
	// convergence parameter dtermined by the eigenvalues of the matrix T from the Golub-Kahn algorithm
      double lambda;
      double T00;
      double T11;
      double T10;
      double eigen_val1;
      double eigen_val2;
            
      T00= dm*dm+fmMinus1*fmMinus1;
      T11=dn*dn+fm*fm;
      T10=dm*fm;
      eigen_val1=(T00+T11+sqrt((T00-T11)*(T00-T11)+4*T10*T10))/2;
      eigen_val2=(T00+T11-sqrt((T00-T11)*(T00-T11)+4*T10*T10))/2;
      lambda=std::min(abs(eigen_val1-T11),abs(eigen_val2-T11));                    
      return lambda;
   }

  // left and right roatations functions
   MatrixTriple right_elementary_rotation(matrixTriple bidiagonalMatrixTriplet, Set<int> j)
   {
      const int colsDiag=bidiagonalMatrixTriplet.diag.cols();  
      const int rowsDiag=bidiagonalMatrixTriplet.diag.rows();
      const int dimU=bidiagonalMatrixTriplet.left.cols();  
      const int dimV=bidiagonalMatrixTriplet.right.rows();
      Vector<double> u(2);
      u[0]=bidiagonalMatrixTriplet.diag[j][j];
      u[1]=bidiagonalMatrixTriplet.diag[j][colsDiag-1];
      Matrix<double> Rij= givens_rot(u);
      Matrix<double> B1=bidiagonalMatrixTriplet.diag.minor(sequence(0,rowsDiag),setj)*Rij;
      bidiagonalMatrixTriplet.diag.minor(sequence(0,rowsDiag),setj)=B1;
      Matrix<double> V1=bidiagonalMatrixTriplet.right.minor(sequence(0,dimV),setj)*Rij; 
      bidiagonalMatrixTriplet.right.minor(sequence(0,dimV),setj)=V1;
      return bidiagonalMatrixTriplet;
      
   }
   
   MatrixTriple left_elementary_rotation(matrixTriple bidiagonalMatrixTriplet, Set<int> j)
   {
      const int colsDiag=bidiagonalMatrixTriplet.diag.cols();  
      const int rowsDiag=bidiagonalMatrixTriplet.diag.rows();
      const int dimU=bidiagonalMatrixTriplet.left.cols();  
      const int dimV=bidiagonalMatrixTriplet.right.rows();
      Vector<double> u(2);
      u[0]=bidiagonalMatrixTriplet.diag[j][j];
      u[1]=bidiagonalMatrixTriplet.diag[i][j];
      Matrix<double> Rij= givens_rot(u);
      const Matrix<double> B2=Rij*bidiagonalMatrixTriplet.diag.minor(setj,sequence(0,colsDiag)); 
      bidiagonalMatrixTriplet.diag.minor(setj,sequence(0,colsDiag))=B2;
      const Matrix<double> U1=Rij*bidiagonalMatrixTriplet.left.minor(setj,sequence(0,dimU)); 
      bidiagonalMatrixTriplet.left.minor(setj,sequence(0,dimU))=U1;
      return bidiagonalMatrixTriplet;  
   }

   matrixTriple jacobi_rotation(matrixTriple bidiagonalMatrixTriplet)
   {
      const int colsDiag=bidiagonalMatrixTriplet.diag.cols();  
      const int rowsDiag=bidiagonalMatrixTriplet.diag.rows();
      const int dimU=bidiagonalMatrixTriplet.left.cols();  
      const int dimV=bidiagonalMatrixTriplet.right.rows();
      for (int i=0; i<colsDiag; i++) {
              if (abs(bidiagonalMatrixTriplet.diag[i][i])<epsilon){
               if (i==colsDiag-1) {
                  for (int j=colsDiag-2; j>=0; j=j-1)   {
                     Set<int> setj(j);
                     setj+=colsDiag-1;
                     bidiagonalMatrixTriplet=right_elementray_rotation(bidiagonalMatrixTriplet,j);
                     
                  }
               }
               else{                      
                  for (int j=i+1; j<=colsDiag-1; j++)   {
                     Set<int> setj(i);
                      bidiagonalMatrixTriplet=left_elementray_rotation(bidiagonalMatrixTriplet,j);
                  }  
               }
            }
         }
      return bidiagonalMatrixTriplet;    
   }

   matrixTriple Golub_kahn_step(matrixTriple bidiagonalMatrixTriplet)
   {
      //variables named according to the algorithm given in "Matrix computations" from Golub
      const int colsDiag=bidiagonalMatrixTriplet.diag.cols();  
      const int rowsDiag=bidiagonalMatrixTriplet.diag.rows();
      const int dimU=bidiagonalMatrixTriplet.left.cols();  
      const int dimV=bidiagonalMatrixTriplet.right.rows();
      double lambda;
      double dm =bidiagonalMatrixTriplet.diag[rowsM-2][colsM-2];
      double fm=bidiagonalMatrixTriplet.diag[rowsM-2][colsM-1];
      double dn=bidiagonalMatrixTriplet.diag[rowsM-1][colsM-1];
      lambda=rowsM > 2 ? eigenValuesOfT(dm,dn,fm,bidiagonalMatrixTriplet.diag[rowsM-3][colsM-2]) : 0;
      for (int i=0; i<=colsDiag-2; i++) {
            Set<int> setij(i);
            setij += i+1;
            u[0]=bidiagonalMatrixTriplet.diag[i][i]*bidiagonalMatrixTriplet.diag[i][i]-lambda;
            u[1]=bidiagonalMatrixTriplet.diag[i][i]*bidiagonalMatrixTriplet.diag[i][i+1];

            Matrix<double> Rij= givens_rot(u);
            const Matrix<double> B1=bidiagonalMatrixTriplet.diag.minor(sequence(0,rowsDiag),setij)*Rij; 
            bidiagonalMatrixTriplet.diag.minor(sequence(0,rowsDiag),setij)=B1;

            const Matrix<double> V1=bidiagonalMatrixTriplet.right.minor(sequence(0,dimV),setij)*Rij; 
            bidiagonalMatrixTriplet.right.minor(sequence(0,dimV),setij)=V1;
            u[0]=bidiagonalMatrixTriplet.diag[i][i];
            u[1]=bidiagonalMatrixTriplet.diag[i+1][i];
 
            Rij= givens_rot(u);
            Matrix<double> B2=T(Rij)*bidiagonalMatrixTriplet.diag.minor(setij,sequence(0,colsDiag)); 
             bidiagonalMatrixTriplet.diag.minor(setij,sequence(0,colsDiag))=B2;
            
            Matrix<double> U1=T(Rij)*bidiagonalMatrixTriplet.left.minor(setij,sequence(0,dimU)); 
            bidiagonalMatrixTriplet.left.minor(setij,sequence(0,dimU))=U1;
         }
      return bidiagonalMatrixTriplet;
   }
   
   SingularValueDecomposition output_conversion_svd(matrixTriple bidiagonalMatrixTriplet)
   {
      const int colsDiag=bidiagonalMatrixTriplet.diag.cols();  
      const int rowsDiag=bidiagonalMatrixTriplet.diag.rows();
      SparseMatrix<double> Diag(rowsDiag,colsDiag);
      for (int i=0; i<=colsDiag-1; i++)
         {
            Diag[i][i]=bidiagonalMatrixTriplet.diag[i][i];
         }
       
      SingularValueDecomposition Out;
       if (colsM>rowsM){
          Out.sigma=T(Diag);
          Out.left_companion=T(bidiagonalMatrixTriplet.right);
          Out.right_companion=bidiagonalMatrixTriplet.left;
         }
       else{
          Out.sigma=Diag;
          Out.left_companion=T(bidiagonalMatrixTriplet.left);
          Out.right_companion=bidiagonalMatrixTriplet.right;
       }
       return Out;
       
   }
   
   SingularValueDecomposition singular_value_decomposition(Matrix<double> M)
   { 
      const int colsM=M.cols();  
      const int rowsM=M.rows();
       double max_entry=0;
      for (int i=0; i<rowsM-1; i++){ 
         for (int j=0; j<colsM-1; j++){
            if(abs(M[i][j])>max_entry){
               max_entry=abs(M[i][j]);
            }          
         }
      }
      if (colsM>rowsM)
         {
            Matrix<double> M1=T(M);
            M=M1;          
         }
      matrixTriple bidiagonalMatrixTriplet=bidiag(M);
      const int colsDiag=bidiagonalMatrixTriplet.diag.cols();  
      const int rowsDiag=bidiagonalMatrixTriplet.diag.rows();
      const int dimU=bidiagonalMatrixTriplet.left.cols();  
      const int dimV=bidiagonalMatrixTriplet.right.rows();
        
      Vector<double> u(2);
      int fuse=1;
      while (fuse>0) {
         fuse=0;
         bidiagonalMatrixTriplet=jacobi_rotation(bidiagonalMatrixTriplet);
         bidiagonalMatrixTriplet=golub_kahn_step(bidiagonalMatrixTriplet);
         
         //exception catching
         for (int i=0; i<=colsDiag-2; i++) {
            double left=abs(bidiagonalMatrixTriplet.diag[i][i+1]);
            double right=epsilon*colsM*rowsM*max_entry;
            if (left<=right)
               {
                  bidiagonalMatrixTriplet.diag[i][i+1]=0;
               }
            if (left>right){
               fuse=1;
               break;
            }
         }
      }
       return output_conversion_svd(bidiagonalMatrixTriplet);
   }
   
   
   Matrix<double> householder_trafo(const Vector<double>& v)
   {
      Matrix<double> Mhouse;
      const int dimv=v.dim();
      double max_entry=0;
      for (int i=0; i<dimv; i++){ 
         if(abs(v[i])>max_entry){
            max_entry=abs(v[i]);
         }          
      }
      const double zero=epsilon*dimv*max_entry;
      Vector<double> u=v+non_zero_sign(v[0])*sqrt(v*v)*unit_vector<double>(dimv,0);

      if (u*u<=zero*zero) {
         Mhouse=unit_matrix<double>(dimv);
      } else {
         u/=sqrt(u*u);
         Mhouse=2*vector2col(u)*vector2row(u)-unit_matrix<double>(dimv);
      }
      return Mhouse;
   }
   

   std::pair< Matrix<double>,Matrix<double> > qr_decomp(Matrix<double> M)
   {
      //exeption
      const int colsM=M.cols()-1; 
      const int rowsM=M.rows()-1;
      Matrix<double> Q=unit_matrix<double>(rowsM+1);
      const int dimQ=Q.cols()-1;
      for (int i=0; i<=colsM; i++) 
      {
         Vector<double>v=M.col(i).slice(i);
         Matrix<double>Qi=householder_trafo(v);
         Matrix<double>M1=Qi*M.minor(range(i,rowsM),range(i,colsM));
         M.minor(range(i,rowsM),range(i,colsM))=M1;
         Matrix<double>Q1=Qi*Q.minor(range(i,dimQ),range(0,dimQ)); 
         Q.minor(range(i,dimQ),range(0,dimQ))=Q1;
      } 
      return std::pair<Matrix<double>,Matrix<double> >(T(Q),M);
   }

   
   Matrix<double> moore_penrose_inverse(const Matrix<double>& M)
   {
      SingularValueDecomposition bidiagonalMatrixTriplet=singular_value_decomposition(M);
      const int colsDiag=bidiagonalMatrixTriplet.sigma.cols();  
      const int rowsDiag=bidiagonalMatrixTriplet.sigma.rows();
      double max_entry_Diag=0;
      for (int i=0; i<std::min(colsDiag,rowsDiag); i++){ 
         if(abs(bidiagonalMatrixTriplet.sigma[i][i])>max_entry_Diag){
            max_entry_Diag=abs(bidiagonalMatrixTriplet.sigma[i][i]);
         }          
      }
      double zero=epsilon*std::max(colsDiag,rowsDiag)*max_entry_Diag;
      for (int i=0; i<std::min(colsDiag,rowsDiag); i++){ 
         if(abs(bidiagonalMatrixTriplet.sigma[i][i])>zero){
            bidiagonalMatrixTriplet.sigma[i][i]=1/bidiagonalMatrixTriplet.sigma[i][i];
         }          
      }
      Matrix<double> pseudo_inv=bidiagonalMatrixTriplet.right_companion*T(bidiagonalMatrixTriplet.sigma)*T(bidiagonalMatrixTriplet.left_companion);
      return pseudo_inv;
   }

   Vector<double> lin_solve(Matrix<double> A, Vector<double> b)
   {
      Vector<double> x= moore_penrose_inverse(A)*b;
      return x;
   }
    
   Vector<double> eigenvalues(Matrix<double> M)
   // computes a vector tof eigenvalues only for  square positive-semidefinte matrix
   { 
      SingularValueDecomposition Mdecomp=singular_value_decomposition(M);
      return Mdecomp.sigma.diagonal();
   }
 
}

// end namespace pm

// Local Variables:
// mode:C++
// c-basic-offset:3
// indent-tabs-mode:nil
// End:
