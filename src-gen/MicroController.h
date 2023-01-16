#ifndef ROBOCALC_CONTROLLERS_MICROCONTROLLER_H_
#define ROBOCALC_CONTROLLERS_MICROCONTROLLER_H_

#include "Vehicle.h"
#include "RoboCalcAPI/Controller.h"
#include "DataTypes.h"

#include "Movement.h"

class MicroController: public robocalc::Controller 
{
public:
	MicroController(Vehicle& _platform) : platform(&_platform){};
	MicroController() : platform(nullptr){};
	
	~MicroController() = default;
	
	void Execute()
	{
		movement.execute();
	}
	
	struct Channels
	{
		MicroController& instance;
		Channels(MicroController& _instance) : instance(_instance) {}
		
		EventBuffer* tryEmitTurn(void* sender, std::tuple<Angle> args)
		{
			if(instance.movement.canReceiveTurn(args))
				instance.movement.turn_in.trigger(sender, args);
				
			return &instance.movement.turn_in;
		}
		
		EventBuffer* tryEmitObstacle(void* sender, std::tuple<Loc> args)
		{
			if(instance.movement.canReceiveObstacle(args))
				instance.movement.obstacle_in.trigger(sender, args);
				
			return &instance.movement.obstacle_in;
		}
		
		EventBuffer* tryEmitFlag(void* sender, std::tuple<> args)
		{
			flag_in.trigger(sender, args);
			return &flag_in;
		}
		
		EventBuffer* tryEmitResume(void* sender, std::tuple<> args)
		{
			if(instance.movement.canReceiveResume(args))
				instance.movement.resume_in.trigger(sender, args);
				
			return &instance.movement.resume_in;
		}
		
		EventBuffer* tryEmitStop(void* sender, std::tuple<> args)
		{
			if(instance.movement.canReceiveStop(args))
				instance.movement.stop_in.trigger(sender, args);
				
			return &instance.movement.stop_in;
		}
		
		EventBuffer* tryEmitOdometer(void* sender, std::tuple<double> args)
		{
			if(instance.movement.canReceiveOdometer(args))
				instance.movement.odometer_in.trigger(sender, args);
				
			return &instance.movement.odometer_in;
		}
		
		struct Flag_t : public EventBuffer
		{
			THREAD_SAFE_ONLY(std::mutex _mutex;)
			std::tuple<> _args;
			void* _sender = nullptr;
			void* getSender() override
			{
				THREAD_SAFE_ONLY(std::lock_guard<std::mutex> lock{_mutex};)
				return _sender;
			}
			
			void reset() override
			{
				THREAD_SAFE_ONLY(std::lock_guard<std::mutex> lock{_mutex};)
				_sender = nullptr;
			}
			
			void trigger(void* sender, std::tuple<> args)
			{
				THREAD_SAFE_ONLY(std::lock_guard<std::mutex> lock{_mutex};)
				_sender = sender;
			}
		} flag_in;
	};
	
	Channels channels{*this};
	
	Vehicle* platform;
	Movement_StateMachine<MicroController> movement{*platform, *this, &movement};
};

#endif
