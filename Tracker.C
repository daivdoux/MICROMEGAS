// Written by Marion LEHUARUX (2018)
// ---------------------------------------------------------------------------------
// ---------------------------------------------------------------------------------
// TL MICROMEGAS TRACKER
// ---------------------------------------------------------------------------------
// ---------------------------------------------------------------------------------
//comment on s'en sert
// ---------------------------------------------------------------------------------
#include <iostream>
#include <fstream>
#include <vector>
#include <list>
#include "TString.h"
#include "TEventList.h"
#include "TEntryList.h"
#include "TMath.h"
#include "TCanvas.h"
#include "TLegend.h"
#include "TH1.h"
#include "TH2.h"
#include "TF1.h"
#include "TStyle.h"
#include <TROOT.h>
#include <sys/stat.h>
#include <TLegend.h>
#include <TProfile.h>
#include <boost/progress.hpp>
#include <boost/timer.hpp>
#include "TGraph2D.h"
#include "TBuffer.h"
#include "TBranch.h"
#include "TTree.h"
#include "TAxis.h"
#include <cmath>
#include <algorithm>
#include "TMinuit.h"

using namespace std;

class Point {
  double x, y, z;
 public:
  void setPoint (double, double, double);
  void deplace (double, double, double);
  void print ();
  double coordx ();
  double coordy ();
  double coordz ();
};

void Point::setPoint(double a, double b, double c) {
    x = a; y = b ;  z = c; 
}

void Point::deplace (double dx , double dy, double dz) {
    x += dx; y += dy; z += dz; 
}


void Point::print () {
    cout << x << "      " << y << "      " << z << endl;
}

double Point::coordx() {    
    return(x);
}
double Point::coordy() {    
    return(y);
}
double Point::coordz() {    
    return(z);
}

Point aVect(Point P, double a){
    Point R;
    R.setPoint(a*P.coordx(), a*P.coordy(), a*P.coordz());
    return(R);
}

Point dir (Point P, Point Q) {
    Point R;
    R.setPoint(Q.coordx()-P.coordx(), Q.coordy()-P.coordy(), Q.coordz()-P.coordz());
    return(R);
}

Point prod_vect(Point P, Point Q) {
    Point R;
    Double_t x, y, z;
    x = Q.coordy()*P.coordz()-P.coordz()*Q.coordy();
    y = Q.coordz()*P.coordx()-P.coordx()*Q.coordz();    
    z = Q.coordx()*P.coordy()-P.coordy()*Q.coordx();
    R.setPoint(x, y, z);
    return(R);
}

double prod_scal(Point P, Point Q){
    return(P.coordx()*Q.coordx()+ P.coordy()*Q.coordy()+P.coordz()*Q.coordz());
}

Point inBetween(Point P, Point Q){
    Point R;
    R.setPoint(Q.coordx()+P.coordx(), Q.coordy()+P.coordy(), Q.coordz()+P.coordz());
    R = aVect(R, 0.5);
    return(R);
}

Point PointTh (Point P, Point Q, int m) {
    // on relie les points P et Q pour trouver l'équation de droite et
    // on cherche le point théorique attendu sur le micromegas m 
    Double_t zm[4] = {0., -52.6, -79.1, -136.6};
    Point R;
    Point vec = dir(P, Q);
    double t = (zm[m-1]-P.coordz())/vec.coordz();
    R.setPoint(vec.coordx()*t+P.coordx(), vec.coordy()*t+P.coordy(), zm[m-1]);
    return(R);
}

Point PointThDOCA (Point P, Point Q, double z) {
    // on relie les points P et Q pour trouver l'équation de droite et
    // on cherche le point théorique attendu sur le micromegas m 
    Double_t zm[4] = {0., -52.6, -79.1, -136.6};
    Point R;
    Point vec = dir(P, Q);
    double t = (z-P.coordz())/vec.coordz();
    R.setPoint(vec.coordx()*t+P.coordx(), vec.coordy()*t+P.coordy(), z);
    return(R);
}

double dist(Point P, Point Q) {
    Point vec = dir(P, Q);
    double d=sqrt(prod_scal(vec, vec));
    return(d);
}


double angle(Point A, Point B, Point C, Point D){
    Point d1 = dir(A, B);
    Point d2 = dir(C, D);
    double costheta = prod_scal(d1, d2)/(dist(A, B)*dist(C,D));
    double theta = acos(costheta);
    return(theta);
}

vector<Point> findDOCA(Point A, Point B, Point C, Point D)
{
    // On ecrit que le produit scalaire avec les deux vecteurs directeur est nul et on resoud
    // le systeme de Cramer
    Point O, N;
    O.setPoint(0., 0., 0.);
    Point v1 = dir(A, B);
    Point v2 = dir(D, C);
    vector<Point> result;
    double lambda, mu;
    double a, b, c, d, e, f;
    a = -(v1.coordx()*v1.coordx() + v1.coordy()*v1.coordy() + v1.coordz()*v1.coordz());
    b = prod_scal(v1, v2);
    c = -prod_scal(v1, v2);
    d =  v2.coordx()*v2.coordx() + v2.coordy()*v2.coordy() + v2.coordz()*v2.coordz();
    e = -(D.coordx()-A.coordx())*v1.coordx() - (D.coordy()-A.coordy())*v1.coordy() - (D.coordz()-A.coordz())*v1.coordz();
    f = -(D.coordx()-A.coordx())*v2.coordx() - (D.coordy()-A.coordy())*v2.coordy() - (D.coordz()-A.coordz())*v2.coordz();

    double det = a*d-b*c;
    if (det==0.) {
        result.push_back(O);
        result.push_back(O);
        return(result);
    }

    else{
        lambda = (e*d-f*b)/det;
        mu = (a*f-c*e)/det;

        Point P1;
        Point P2;
        P1.setPoint(A.coordx() + v1.coordx()*lambda, A.coordy() + v1.coordy()*lambda, A.coordz() + v1.coordz()*lambda);
        P2.setPoint(D.coordx() + v2.coordx()*mu, D.coordy() + v2.coordy()*mu, D.coordz() + v2.coordz()*mu);
        // if (isnan(P1.coordx())) {
        //     cout << "Problem here !!!" << endl;
        //     cout << A.coordx() << "     " << A.coordy() << "     " << A.coordz()<< endl;
        //     cout << B.coordx() << "     " << B.coordy() << "     " << B.coordz()<< endl;
        //     cout << C.coordx() << "     " << C.coordy() << "     " << C.coordz()<< endl;
        //     cout << D.coordx() << "     " << D.coordy() << "     " << D.coordz()<< endl;
        //     cout << "Lambda.   " << lambda << "   " << "Mu.   " << mu << endl;
        //     cout << "a.   " << a << "   " << "b.   " << b << endl;  
        //     cout << "c.   " << c << "   " << "d.   " << d << endl;
        //     cout << "e.   " << e << "   " << "f.   " << f << endl; 
        // } 
        result.push_back(P1);
        result.push_back(P2);
        return(result);
    }
}

double Contrast(TH2D * histo, double pix, int nbin)
{
double d = 50;
int n_pix = floor(d/pix);
int n = floor(nbin*pix/d); 
double I[n_pix][n_pix];
double min = histo->Integral();
double max = 0.;
for (int i=0; i < n_pix; i++){
    for (int j=0; j < n_pix; j++){
        double temp = 0.;
        for (int x = i*n; x < (i+1)*n; x++){
            for (int y = j*n; y < (j+1)*n; y++){
                temp = temp + histo->GetBinContent(x, y);
            }
        }
        I[i][j] = temp;   
        if (temp < min && temp!=0.) min = temp;
        else if (temp >= max) max = temp;
        // cout << max << "    " << min << endl;
    }

}

return((max-min)/(max+min));
}

// Gaussian function
Double_t fgauss(Double_t *x, Double_t *par)
{
    Double_t arg = 0;
    if (par[2] != 0) arg = (x[0] - par[1])/par[2];

    Double_t fitval = par[0]*TMath::Exp(-0.5*arg*arg);
    return fitval;
}

void Align(int nevt){
gStyle->SetOptStat(0);

TFile* file = TFile::Open( "TL_cos_analyse_HELP_WE.root" );
TTree* tree = (TTree*)file->Get("T");
cout << "Tree opened!" << endl;
Double_t MGv2_ClusPos[8][300];
Double_t MGv2_ClusSize[8][300];
Int_t evn;
Int_t n = tree->GetEntries();

tree->SetBranchAddress("evn", &evn);
tree->SetBranchAddress("MGv2_ClusPos", &MGv2_ClusPos);
tree->SetBranchAddress("MGv2_ClusSize", &MGv2_ClusSize);

Double_t  M1Z = 0.0;
Double_t  M2Z = -52.6;
Double_t  M3Z = -79.1;
Double_t  M4Z = -136.6;
Double_t MdZ = 1.0;

Double_t conv = 50/1037.0;
Point O;
O.setPoint(0., 0., 0.);

TH1F *h1 = new TH1F("h1", "dX MICROMEGAS 2", 100, -2., 2.);
h1->GetXaxis()->SetTitle("dX (cm)");
h1->GetYaxis()->SetTitle("Number of events");
TH1F *h2 = new TH1F("h2", "dY MICROMEGAS 2", 100, -2., 2.);
h2->GetXaxis()->SetTitle("dY (cm)");
h2->GetYaxis()->SetTitle("Number of events");
TH1F *h3 = new TH1F("h3", "dX MICROMEGAS 3", 100, -2., 2.);
h3->GetXaxis()->SetTitle("dX (cm)");
h3->GetYaxis()->SetTitle("Number of events");
TH1F *h4 = new TH1F("h4", "dY MICROMEGAS 3", 100, -2., 2.);
h4->GetXaxis()->SetTitle("dY (cm)");
h4->GetYaxis()->SetTitle("Number of events");

boost::progress_display show_progress(nevt);
// for ( int i = 0; i < n; ++i) // Loop over the events 
for ( int i = 0; i < nevt  ; ++i){ // Loop over the events 
        ++show_progress;
        tree->GetEntry(i);
        Int_t m(0);
        vector<Point> M1, M2, M3, M4;
        vector<Point> dM1, dM2, dM3, dM4;
        Point P1, P2, P3, P4;
        Point dP1, dP2, dP3, dP4;
        for ( int j = 0; j < 10; ++j){ // Loop over the multiple hits of the event
            if (MGv2_ClusPos[0][j]+MGv2_ClusPos[1][j]==0 ||MGv2_ClusPos[2][j]+MGv2_ClusPos[3][j]==0 ||MGv2_ClusPos[4][j]+MGv2_ClusPos[5][j]==0 ||MGv2_ClusPos[6][j]+MGv2_ClusPos[7][j] == 0. || MGv2_ClusSize[0][j] < 1 || MGv2_ClusSize[1][j] < 1 || MGv2_ClusSize[2][j] < 1 || MGv2_ClusSize[3][j] < 1 || MGv2_ClusSize[4][j] < 1 ||MGv2_ClusSize[5][j] < 1|| MGv2_ClusSize[6][j] < 1 || MGv2_ClusSize[7][j] < 1 ) break; // 4hits et multiplexage avoid nan
            else{
                ++m;
                P1.setPoint(MGv2_ClusPos[0][j]*conv, MGv2_ClusPos[1][j]*conv, M1Z);
                P2.setPoint(MGv2_ClusPos[2][j]*conv, MGv2_ClusPos[3][j]*conv, M2Z);
                P3.setPoint(MGv2_ClusPos[4][j]*conv, MGv2_ClusPos[5][j]*conv, M3Z);
                P4.setPoint(MGv2_ClusPos[6][j]*conv, MGv2_ClusPos[7][j]*conv, M4Z);

                dP1.setPoint(MGv2_ClusSize[0][j]*conv, MGv2_ClusSize[1][j]*conv, MdZ);
                dP2.setPoint(MGv2_ClusSize[2][j]*conv, MGv2_ClusSize[3][j]*conv, MdZ);
                dP3.setPoint(MGv2_ClusSize[4][j]*conv, MGv2_ClusSize[5][j]*conv, MdZ);
                dP4.setPoint(MGv2_ClusSize[6][j]*conv, MGv2_ClusSize[7][j]*conv, MdZ);

                M1.push_back(P1);
                M2.push_back(P2);
                M3.push_back(P3);
                M4.push_back(P4);

                dM1.push_back(dP1);
                dM2.push_back(dP2);
                dM3.push_back(dP3);
                dM4.push_back(dP4);
            }
        }
        // cout << "Multiplicite : " << m << endl;
        for  ( int k = 0; k < m; ++k){
            for  ( int l = 0; l < m; ++l){
                for  ( int p = 0; p < m; ++p){
                    for  ( int q = 0; q < m; ++q){
                        // if distance du point th M1-M4 à un point de M2 et M3 < sqrt(dx^2+dy^2) du point alors track bim bam boum    
                        Point int2 = PointTh(M1[k], M4[l], 2);
                        Point int3 = PointTh(M1[k], M4[l], 3);
                        // cout << "dev M2 " << dist(O, dM2[p]) << endl;
                        // cout << "dev M3 " << dist(O, dM3[p]) << endl;
                        if (dist(M2[p], int2) < 0.5*dist(O, dM2[p]) && dist(M3[q], int3) < 0.5*dist(O, dM3[q])){
                            
                            // cout << "Track pas déviée : "<< i << "    " << k << "    " << p << "    " << q << "    " << l << endl;
                            
                            double dx2 = M2[p].coordx() - int2.coordx();
                            double dy2 = M2[p].coordy() - int2.coordy();
                            // cout << dx2 << "    " << dy2 << endl;
                            double dx3 = M3[q].coordx() - int3.coordx();
                            double dy3 = M3[q].coordy() - int3.coordy();
                            // cout << dx3 << "    " << dy3 << endl;
                            h1->Fill(dx2);
                            h2->Fill(dy2);
                            h3->Fill(dx3);
                            h4->Fill(dy3);
                        }
                    }
                }
            }
        }

}

// Merci David! (CopyRight FitMCA.C)
TF1 *fitFcn1 = new TF1("fitFcn1",fgauss, -5., 5., 3);
fitFcn1->SetNpx(500);
fitFcn1->SetLineColor(kRed);

Double_t mean1 = (Double_t) h1->GetMean();
Double_t rms1  = (Double_t) h1->GetRMS();
Double_t max1  = (Double_t) h1->GetMaximum();

fitFcn1->SetParameters( max1, mean1, rms1 );
fitFcn1->SetParNames( "Constant", "Mean Value", "Sigma" );

h1->Fit(fitFcn1,"","", -5., 5.);
//  --------------------------------------------------------
TF1 *fitFcn2 = new TF1("fitFcn2",fgauss, -5., 5., 3);
fitFcn2->SetNpx(500);
fitFcn2->SetLineColor(kRed);

Double_t mean2 = (Double_t) h2->GetMean();
Double_t rms2  = (Double_t) h2->GetRMS();
Double_t max2  = (Double_t) h2->GetMaximum();

fitFcn2->SetParameters( max2, mean2, rms2 );
fitFcn2->SetParNames( "Constant", "Mean Value", "Sigma" );

h2->Fit(fitFcn2,"","", -5., 5.);
//  --------------------------------------------------------
TF1 *fitFcn3 = new TF1("fitFcn3",fgauss, -5., 5., 3);
fitFcn3->SetNpx(500);
fitFcn3->SetLineColor(kRed);

Double_t mean3 = (Double_t) h3->GetMean();
Double_t rms3  = (Double_t) h3->GetRMS();
Double_t max3  = (Double_t) h3->GetMaximum();

fitFcn3->SetParameters( max3, mean3, rms3 );
fitFcn3->SetParNames( "Constant", "Mean Value", "Sigma" );

h3->Fit(fitFcn3,"","", -5., 5.);
//  --------------------------------------------------------
TF1 *fitFcn4 = new TF1("fitFcn4",fgauss, -5., 5., 4);
fitFcn4->SetNpx(500);
fitFcn4->SetLineColor(kRed);

Double_t mean4 = (Double_t) h4->GetMean();
Double_t rms4  = (Double_t) h4->GetRMS();
Double_t max4  = (Double_t) h4->GetMaximum();

fitFcn4->SetParameters( max4, mean4, rms4 );
fitFcn4->SetParNames( "Constant", "Mean Value", "Sigma" );

h4->Fit(fitFcn4,"","", -5., 5.);
//  --------------------------------------------------------
TCanvas *c = new TCanvas("c","",0,0,800,800);
c->Divide(2,2);
c->cd(1);
gPad->SetTopMargin(0);
gPad->SetLeftMargin(0.18);
gPad->SetRightMargin(0.035);
h1->Draw();
fitFcn1->Draw("same");
c->cd(2);
gPad->SetTopMargin(0);
gPad->SetLeftMargin(0.18);
gPad->SetRightMargin(0.035);
h2->Draw();
fitFcn2->Draw("same");
c->cd(3);
gPad->SetTopMargin(0);
gPad->SetLeftMargin(0.18);
gPad->SetRightMargin(0.035);
h3->Draw();
fitFcn3->Draw("same");
c->cd(4);
gPad->SetTopMargin(0);
gPad->SetLeftMargin(0.18);
gPad->SetRightMargin(0.035);
h4->Draw();
fitFcn4->Draw("same");
c->SaveAs(("Alignement_" + to_string(nevt) + ".pdf").c_str());  
c->Close();
}  


void Tracker( string object ){
gStyle->SetOptStat(0);

// TFile* file = TFile::Open( "TL_2017_cos_analyse_1819.root" );
// TFile* file = TFile::Open( "TL_2017_cos_analyse_1920.root" );
// TFile* file = TFile::Open( "TL_2017_cos_analyse_2021.root" );
// TFile* file = TFile::Open( "TL_2017_cos_analyse_2122.root" );


// TFile* file = TFile::Open( "TL_cos_analyse_apple.root" );
// TFile* file = TFile::Open( "TL_cos_analyse_PYRAMIDE.root" );
TFile* file = TFile::Open( "TL_cos_analyse_A.root" );
// TFile* file = TFile::Open( "TL_cos_analyse_SMILEY2.root" );
// TFile* file = TFile::Open( "TL_cos_analyse_HELP_WE.root" );

TTree* tree = (TTree*)file->Get("T");
cout << "Tree opened!" << endl;
Double_t MGv2_ClusPos[8][300];
Double_t MGv2_ClusSize[8][300];
Int_t evn;
double conv_rad_deg = 180./3.14159265;
Int_t n = tree->GetEntries();

tree->SetBranchAddress("evn", &evn);
tree->SetBranchAddress("MGv2_ClusPos", &MGv2_ClusPos);
tree->SetBranchAddress("MGv2_ClusSize", &MGv2_ClusSize);

Double_t C_projX, C_projY;

// Si données de 2018 
Double_t M1Z = 0.0;
Double_t M2Z = -52.6;
Double_t M3Z = -79.1;
Double_t M4Z = -136.6;

// Si données de 2017 : (commenter l'alignement fait pour le setup 2018)
// Double_t M1Z = 0.0;
// Double_t M2Z = -52.5;
// Double_t M3Z = -79;
// Double_t M4Z = -126.5;

// Double_t M1Z = 0.0;
// Double_t M2Z = -47.5;
// Double_t M3Z = -74.;
// Double_t M4Z = -126.5;


//  souci avec les données de 2017


Double_t Zp = -70.; //Z plateau 
Double_t Zb = 10. ;//Z brique 
Double_t MdZ = 1.0;

Double_t conv = 50./1037.;
Point O, N;
N.setPoint(0., 0., 1.);
O.setPoint(0., 0., 0.);
int n_track_non_dev(0);
int n_track_dev(0);

// ------------------------- Alignement ---------------------------------
//  Fit sur non deviés parmis 500000 points de HELP WE 
Double_t dx2, dx3, dy2, dy3;
dx2 = -1.29731e-02;
dx3 = -5.90414e-02;
dy2 = -7.11587e-02;
dy3 = -2.82983e-02;
// ----------------------------------------------------------------------
// Paramètres limites
Double_t lim = 1. ;
Double_t lim_theta = 15.;
Int_t nbin = 150;
// ----------------------------------------------------------------------

TH2D *h2d = new TH2D("h2d","", nbin,0,50,nbin,0,50);
TH2D *h2d1 = new TH2D("h2d1","", nbin,0,50,nbin,0,50);//, 2*nbin/5, -70, -50);

TH2D *test = new TH2D("test","", nbin/5, -70, -60, nbin, 0, 50);
TH2D *test1 = new TH2D("test1","", nbin,0,50, nbin/5, -70, -60);

TH1D *h1d = new TH1D("h1d","Distribution of the deviation angle", 100, 0, 20);
TH1D *inc = new TH1D("inc","Muons incidence angle", 100, 0.,30.);

boost::progress_display show_progress(n);
for ( int i = 0; i < n; ++i){ // Loop over the events 
// for ( int i = 0; i < 20000  ; ++i){ // Loop over the events 
        ++show_progress;
        tree->GetEntry(i);
        Int_t m(0);
        vector<Point> M1, M2, M3, M4;
        vector<Point> dM1, dM2, dM3, dM4;
        Point P1, P2, P3, P4;
        Point dP1, dP2, dP3, dP4;
        for ( int j = 0; j < 10; ++j){ // Loop over the multiple hits of the event
            if (MGv2_ClusPos[0][j]+MGv2_ClusPos[1][j]==0 ||MGv2_ClusPos[2][j]+MGv2_ClusPos[3][j]==0 ||MGv2_ClusPos[4][j]+MGv2_ClusPos[5][j]==0 ||MGv2_ClusPos[6][j]+MGv2_ClusPos[7][j] == 0. || MGv2_ClusSize[0][j] < 1 || MGv2_ClusSize[1][j] < 1 || MGv2_ClusSize[2][j] < 1 || MGv2_ClusSize[3][j] < 1 || MGv2_ClusSize[4][j] < 1 ||MGv2_ClusSize[5][j] < 1|| MGv2_ClusSize[6][j] < 1 || MGv2_ClusSize[7][j] < 1 ) break; // 4hits et multiplexage avoid nan
            else{
                ++m;
                P1.setPoint(MGv2_ClusPos[0][j]*conv, MGv2_ClusPos[1][j]*conv, M1Z);
                P2.setPoint(MGv2_ClusPos[2][j]*conv, MGv2_ClusPos[3][j]*conv, M2Z);
                P3.setPoint(MGv2_ClusPos[4][j]*conv, MGv2_ClusPos[5][j]*conv, M3Z);
                P4.setPoint(MGv2_ClusPos[6][j]*conv, MGv2_ClusPos[7][j]*conv, M4Z);

                // ------------------------- Si alignement -----------------------------
                // - valeur du fit pour remettre a 0 
                P2.deplace(-dx2, -dy2, 0.);
                P3.deplace(-dx3, -dy3, 0.);
                // ----------------------------------------------------------------------

                dP1.setPoint(MGv2_ClusSize[0][j]*conv, MGv2_ClusSize[1][j]*conv, MdZ);
                dP2.setPoint(MGv2_ClusSize[2][j]*conv, MGv2_ClusSize[3][j]*conv, MdZ);
                dP3.setPoint(MGv2_ClusSize[4][j]*conv, MGv2_ClusSize[5][j]*conv, MdZ);
                dP4.setPoint(MGv2_ClusSize[6][j]*conv, MGv2_ClusSize[7][j]*conv, MdZ);

                M1.push_back(P1);
                M2.push_back(P2);
                M3.push_back(P3);
                M4.push_back(P4);

                dM1.push_back(dP1);
                dM2.push_back(dP2);
                dM3.push_back(dP3);
                dM4.push_back(dP4);
            }
        }
        // cout << "Multiplicite : " << m << endl;
        for  ( int k = 0; k < m; ++k){
            for  ( int l = 0; l < m; ++l){
                for  ( int p = 0; p < m; ++p){
                    for  ( int q = 0; q < m; ++q){
                        // if distance du point th M1-M4 à un point de M2 et M3 < sqrt(dx^2+dy^2) du point alors track bim bam boum    
                        Point int2 = PointTh(M1[k], M4[l], 2);
                        Point int3 = PointTh(M1[k], M4[l], 3);
                        // cout << "dev M2 " << dist(O, dM2[p]) << endl;
                        // cout << "dev M3 " << dist(O, dM3[p]) << endl;
                        if (dist(M2[p], int2) < 0.5*dist(O, dM2[p]) && 0.5*dist(M3[q], int3) < dist(O, dM3[q])){
                        // if (dist(M2[p], int2) < dist(O, dM2[p]) && dist(M3[q], int3) < dist(O, dM3[q])){
                            ++n_track_non_dev;
                            Double_t theta = angle(O, N, M4[l], M1[k]);
                            // inc->Fill(theta*conv_rad_deg);
                            // alternative tangente
                            Point M12;
                            M12.setPoint(M2[p].coordx(), M2[p].coordy(), M1Z);
                            inc->Fill(atan(dist(M12, M1[k])/(M1Z-M2Z))*conv_rad_deg);
                        }
                        else{
                            Double_t DOCA = dist(findDOCA(M1[k], M2[p], M3[q], M4[l])[0], findDOCA(M1[k], M2[p], M3[q], M4[l])[1]);
                            // Ajouter condition DOCA < qqc
                            if (DOCA > lim) {
                                // cout << "Fausse track!" << endl;
                                break;
                            }
                            else{
                                // cout << "DOCA = " << DOCA << endl;
                                Point POCA;
                                // POCA = inBetween(top[POCAsearch[pos][0]], bottom[POCAsearch[pos][1]]);
                                POCA = inBetween(findDOCA(M1[k], M2[p], M3[q], M4[l])[0], findDOCA(M1[k], M2[p], M3[q], M4[l])[1]);
                                if (POCA.coordz() < Zp || POCA.coordz() > Zp+Zb) {
                                    // cout << "Fausse track!" << endl;
                                    break;
                                }
                                else{
                                    // Mesure theta entre les droites 
                                    // Double_t theta_dev = angle(M1[k], POCA, POCA, M4[l]); 
                                    Double_t theta_dev = conv_rad_deg*angle(M1[k], M2[p], M3[q], M4[l]); // parce que why not, to discuss
                                    Double_t theta = conv_rad_deg*angle(O, N, M2[p], M1[k]);
                                    inc->Fill(theta);
                                    h1d->Fill(theta_dev);
                                    // Alternative tan calculation
                                    // Point M12;
                                    // M12.setPoint(M2[p].coordx(), M2[p].coordy(), M1Z);
                                    // inc->Fill(atan(dist(M12, M1[k])/(M1Z-M2Z))*conv_rad_deg);
                                    // ici conditions diffraction max etc;
                                    if (theta_dev > lim_theta){
                                        // cout << "Déviation supérieure a déviation max -> Fausse track!" << endl;
                                        // ici big soucis theta dev max en theorie 0.006...
                                        break;
                                    }
                                    else{
                                    ++n_track_dev;
                                    // cout << min(1., 1./inc->GetBinContent(theta)) << endl;
                                    h2d->Fill(50.-POCA.coordy(), POCA.coordx());//, min(1., 1000./inc->GetBinContent(theta))); // poids test
                                    h2d1->Fill(50.-POCA.coordy(), POCA.coordx(), 70+POCA.coordz()); // poids test
                                    test->Fill(POCA.coordz(), POCA.coordx());
                                    test1->Fill(50.-POCA.coordy(), POCA.coordz());
                                    }
                                }
                            }
                            
                        }
                    }     
                }
            }
        }
    
}

cout << "Nombre d'évènements = " << n << endl;
cout << "Nombre de tracks non déviées = " << n_track_non_dev << endl;
cout << "Nombre de tracks déviées = " << n_track_dev << endl;

TCanvas *canvas2 = new TCanvas("canvas2","",0,0,600,600);
canvas2->cd();
h2d->SetTitle("Reconstruction");
gStyle->SetPalette(kBird);
h2d->SetMinimum(-0.1);
h2d->GetXaxis()->SetTitle("Y (cm)");
h2d->GetYaxis()->SetTitle("X (cm)");
h2d->Draw("COLZ");
canvas2->SaveAs(("Reconstruction_" + object + "_DOCA_" + to_string(lim) + "_theta_"+ to_string(lim_theta) +  ".pdf").c_str());
canvas2->Close();

TCanvas *canvas = new TCanvas("canvas","",0,0,600,600);
canvas->SetTitle("Reconstruction");
canvas->Divide(2,2);
canvas->cd(3);
gStyle->SetPalette(kBird);
cout << h2d->Integral() << endl;
// h2d->SetMinimum(-0.1);
// h2d->GetXaxis()->SetTitle("X (cm)");
// h2d->GetYaxis()->SetTitle("Y (cm)");
h2d->Draw("COLZ");
canvas->cd(1);
TH1D *h1 = h2d->ProjectionX();
h1->SetFillColor(859);
h1->Draw("bar");
C_projX = (h1->GetMaximum() - h1->GetMinimum(0.))/(h1->GetMaximum() + h1->GetMinimum(0.));
canvas->cd(4);
TH1D *h2 = h2d->ProjectionY();
h2->SetFillColor(859);
h2->Draw("hbar");
C_projY = (h2->GetMaximum() - h2->GetMinimum(0.))/(h2->GetMaximum() + h2->GetMinimum(0.));
canvas->Update();
canvas->SaveAs(("Result_" + object + "_DOCA_" + to_string(lim) + "_theta_"+ to_string(lim_theta) +  ".pdf").c_str());
canvas->Close();

TCanvas *canvas1 = new TCanvas("canvas1","",0,0,600,600);
canvas1->cd();
canvas1->SetLeftMargin(0.15);
h1d->SetMinimum(0.);
h1d->GetXaxis()->SetTitle("Deviation angle (deg)");
h1d->GetYaxis()->SetTitle("Number of tracks");
h1d->Draw("hist");
// canvas->Update();
canvas1->SaveAs(("Theta_dev_" + object + "_DOCA_" + to_string(lim) + "_theta_"+ to_string(lim_theta) + ".pdf").c_str()); 
canvas1->Close();

TCanvas *canvas3 = new TCanvas("canvas3","",0,0,600,600);
canvas3->cd();
// canvas3->SetLogx();
// canvas3->SetLogy();
inc->SetMinimum(0.0);
inc->GetXaxis()->SetTitle("Incidence angle (deg)");
inc->GetYaxis()->SetTitle("Number of tracks");
inc->Draw("hist");

TF1  *f1 = new TF1("f1","gaus",0.,30.);
TF1  *f2 = new TF1("f2","[1]*cos([2]*x+[0])*cos([2]*x+[0])",0.,30.);

f1->SetParameter(0, inc->GetMaximum());
f1->SetParameter(1, inc->GetMean());
f1->SetParameter(2, 8.);
f1->SetParLimits(1, 0.8*inc->GetMean(), 1.2*inc->GetMean());
f1->SetParLimits(0, 0.8*inc->GetMaximum(), 1.2*inc->GetMean());

f2->SetParameter(1, inc->GetMaximum());
f2->SetParameter(0, inc->GetMean());
f2->SetParameter(2, 1./9.);
f2->SetParLimits(0, 0.5*inc->GetMean(), 1.5*inc->GetMean());
f2->SetParLimits(1, 0.9*inc->GetMaximum(), 1.1*inc->GetMaximum());
f2->SetParLimits(2, 0.01, 1.);
f2->SetLineColor(kBlue);

inc->Fit(f1, "RB");
inc->Fit(f2, "RB");

f1->Draw("same");
f2->Draw("same");

canvas->Update();
canvas3->SaveAs(("Inc_" + object + ".pdf").c_str()); 
canvas3->Close();

TCanvas *pocapos = new TCanvas("pocapos","",0,0,600,600);
pocapos->SetTitle("Reconstruction");
pocapos->Divide(2,2);
pocapos->cd(2);
gStyle->SetPalette(kBird);
// h2d->SetMinimum(-0.1);
// h2d->GetXaxis()->SetTitle("X (cm)");
// h2d->GetYaxis()->SetTitle("Y (cm)");
h2d->Draw("COLZ");
pocapos->cd(1);
gPad->SetPad(0.4, 0.51, 0.5, 0.99);
test->SetMinimum(-0.1);
// test1->GetXaxis()->SetTitle("Y (cm)");
// test1->GetYaxis()->SetTitle("Z (cm)");
test->Draw("COL");
pocapos->cd(4);
gPad->SetPad(0.51, 0.4, 0.99, 0.5);
test1->SetMinimum(-0.1);
// test->GetXaxis()->SetTitle("X (cm)");
// test->GetYaxis()->SetTitle("Z (cm)");
test1->Draw("COL");
pocapos->Update();
pocapos->SaveAs(("RecoProjPOCA_" + object + "_DOCA_" + to_string(lim) + "_theta_"+ to_string(lim_theta) +  ".pdf").c_str());
pocapos->Close();

TCanvas *canvas5 = new TCanvas("canvas5","",0,0,600,600);
canvas5->cd();
gStyle->SetPalette(kBird);
// h2d1->SetMinimum(-0.1);
h2d1->GetXaxis()->SetTitle("Y (cm)");
h2d1->GetYaxis()->SetTitle("X (cm)");
// h3d->GetZaxis()->SetTitle("Z (cm)");
h2d1->Draw("SURF3");
canvas5->Update();
canvas5->SaveAs(("Plot3D_" + object + "_DOCA_" + to_string(lim) + "_theta_"+ to_string(lim_theta) +  ".pdf").c_str()); 
canvas5->Close();

cout << "------------------------------------------" << endl;
cout << "Limite sur DOCA (cm) = " << lim << endl;
cout << "Limite sur theta dev (deg) = " << lim_theta << endl;
cout << "------------------------------------------" << endl;
cout << "Contraste projX = " << C_projX << endl;
cout << "Contraste projY = " << C_projY << endl;
cout << "------------------------------------------" << endl; 
cout << "Contraste intégré (25cm) = " << Contrast(h2d, 25, nbin) << endl;
cout << "Contraste intégré (5cm) = " << Contrast(h2d, 5, nbin) << endl;
cout << "Contraste intégré (2.5cm) = " << Contrast(h2d, 2.5, nbin) << endl;
cout << "Contraste intégré (1cm) = " << Contrast(h2d, 1, nbin) << endl;

file->Close();

}


  











