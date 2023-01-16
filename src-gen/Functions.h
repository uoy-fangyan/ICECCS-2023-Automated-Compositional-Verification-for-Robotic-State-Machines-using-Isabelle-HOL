
#ifndef ROBOCALC_FUNCTIONS_H_
#define ROBOCALC_FUNCTIONS_H_

#include "DataTypes.h"
#include <vector>
#include <set>

namespace robocalc
{
	namespace functions
	{
		double hdist(Obstacle o);
		Status analysis(std::vector<GasSensor> gs);
		Angle angle(unsigned int x);
		double dist(std::tuple<double, double> p, std::vector<std::tuple<double, double>> obs);
		Status analysis(std::vector<GasSensor> gs);
		Status analysis(std::vector<GasSensor> gs);
		Angle angle(unsigned int x);
		unsigned int card(std::set<> A);
		Angle location(std::vector<GasSensor> gs);
		unsigned int card(std::set<> A);
		bool inOPEZ(std::tuple<double, double> p);
		unsigned int card(std::set<> A);
		bool goreq(null i1, null i2);
		 intensity(std::vector<GasSensor> gs);
		 intensity(std::vector<GasSensor> gs);
		Angle angle(unsigned int x);
		Status analysis(std::vector<GasSensor> gs);
		bool goreq(null i1, null i2);
		bool goreq(null i1, null i2);
		std::tuple<double, double> maneuv(std::tuple<double, double> v);
		Angle location(std::vector<GasSensor> gs);
		double odist(Obstacle o);
		bool goreq(null i1, null i2);
		unsigned int card(std::set<> A);
		Angle angle(unsigned int x);
		 intensity(std::vector<GasSensor> gs);
		std::tuple<double, double> setVel(std::tuple<double, double> v, double setpoint);
		Angle angle(unsigned int x);
		double CDA(std::tuple<double, double> p, std::vector<std::tuple<double, double>> obs, std::tuple<double, double> v);
		Angle location(std::vector<GasSensor> gs);
		Angle location(std::vector<GasSensor> gs);
		Angle location(std::vector<GasSensor> gs);
		unsigned int card(std::set<> A);
		 intensity(std::vector<GasSensor> gs);
		 intensity(std::vector<GasSensor> gs);
		double vdist(Obstacle o);
		Status analysis(std::vector<GasSensor> gs);
		bool goreq(null i1, null i2);
		
		template<typename T>
		std::set<T> set_union(std::set<T> s1, std::set<T> s2)
		{
			std::set<T> ret;
			ret.insert(s1.begin(), s1.end());
			ret.insert(s2.begin(), s2.end());
			return ret;
		}
		
		template<typename T>
		unsigned int size(std::set<T> s)
		{
			return s.size();
		}
	}
}

#endif
